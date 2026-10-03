import VerifiedGarbage.Proof.Argon2.X86.HPrime.Output
import VerifiedGarbage.Proof.Argon2.X86.HPrime.HashCT

/-!
# Argon2 H′ on x86 (32-bit): the output, in two runs

Two runs of H′ with the same public data (`Same`: the stack pointer and the
arguments) write their output through the same addresses: `copy_rel`,
`emit_rel` and `copyRemaining_rel`, from states with the same number of
output bytes written.
-/

namespace VG.Proof.Argon2.X86.HPrime

open VG VG.X86 VG.Spec.Blake2
open VG.Impl.Argon2.X86.HPrime (copy emitPrefix copyRemaining outOff leftOff)
open VG.Proof.Sha256.X86.Stream (Upd Mupd wp_movi wp_mov wp_addi wp_movm contains_addr)

/-- The public data of two runs. -/
structure Same (s₀ s₀' : State) : Prop where
  esp : esp₀ s₀' = esp₀ s₀
  args : ∀ i < 5, arg s₀' i = arg s₀ i

theorem Same.of_pub {s₀ s₀' : State} (h : hPrimeX86.pub s₀ s₀') : Same s₀ s₀' :=
  ⟨h.1.symm, fun i hi => (h.2 i hi).symm⟩

section
variable {s₀ s₀' : State} (q : Same s₀ s₀')
include q

theorem Same.scr_eq : scr s₀' = scr s₀ := q.args 4 (by decide)
theorem Same.op_eq : op s₀' = op s₀ := q.args 2 (by decide)
theorem Same.ol_eq : ol s₀' = ol s₀ := by
  show (arg s₀' 3).toNat = (arg s₀ 3).toNat; rw [q.args 3 (by decide)]
theorem Same.inp_eq : inp s₀' = inp s₀ := q.args 0 (by decide)
theorem Same.inl_eq : inl s₀' = inl s₀ := by
  show (arg s₀' 1).toNat = (arg s₀ 1).toNat; rw [q.args 1 (by decide)]

end

/-! ## `copy` -/

/-- What `copy` needs: the body, `k` bytes of output written, and `n` to copy. -/
def CopyIn (s₀ : State) (k n : Nat) (s : State) : Prop :=
  Body s₀ s ∧ OutPtr s₀ s k ∧ s.gpr .esi = BitVec.ofNat 32 n

/-- The registers after `copy`'s first instructions. -/
def CopyRegs (s₀ : State) (k n : Nat) (t : State) : Prop :=
  t.gpr .esp = esp₀ s₀ ∧ t.gpr .ebx = scr s₀ ∧ t.gpr .edx = scr s₀ + 768 ∧
    t.gpr .edi = op s₀ + BitVec.ofNat 32 k ∧ t.gpr .esi = BitVec.ofNat 32 n

theorem copy_blk {s₀ : State} (hp : Pre s₀) {k n : Nat} {s : State} (h : CopyIn s₀ k n s) :
    WP isa (.block [.mov .edx (.reg .ebx), .alu .add .edx (.imm 768), .mov .edi (.mem (VG.Impl.Sha512.X86.at_ .ebx outOff))])
      s (CopyRegs s₀ k n) := by
  obtain ⟨b, hk, hn⟩ := h
  have hs := hp.scr_fits
  refine wp_mov fun s₁ u₁ => wp_addi fun s₂ u₂ => wp_movm
    (VG.Proof.Sha512.X86.ea_of (B := scr s₀) (by rw [u₂.other _ (by decide), u₁.other _ (by decide), b.ebx])
      outOff)
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr, b.rd, b.wr]
        exact ⟨scrR s₀, by simp [hp.wr], contains_addr (by decide) (by decide) hs⟩)
    fun s₃ u₃ => WP.block_nil ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), b.esp]
  · rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), b.ebx]
  · rw [u₃.other _ (by decide), u₂.gpr, u₁.gpr, b.ebx]
  · rw [u₃.gpr, u₂.mem, u₁.mem]; exact hk
  · rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hn]

theorem copy_rel {s₀ s₀' : State} (hp : Pre s₀) (hp' : Pre s₀') (q : Same s₀ s₀') {k n : Nat} :
    RelCT isa (fun t₁ t₂ => CopyIn s₀ k n t₁ ∧ CopyIn s₀' k n t₂) copy fun _ _ => True := by
  unfold copy
  refine RelCT.seq (rel_taint [.ebx] (fun _ _ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
      rw [h₁.1.ebx, h₂.1.ebx, q.scr_eq]) ⟨_, by taint_decide⟩
    (fun s h => copy_blk hp h) (fun s h => copy_blk hp' h)) ?_
  exact RelCT.taint (A := taint) (τr [.esp, .ebx, .edx, .edi, .esi])
    (fun t₁ t₂ ⟨⟨a₁, b₁, c₁, d₁, e₁⟩, ⟨a₂, b₂, c₂, d₂, e₂⟩⟩ => agree_regs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · rw [a₁, a₂, q.esp]
      · rw [b₁, b₂, q.scr_eq]
      · rw [c₁, c₂, q.scr_eq]
      · rw [d₁, d₂, q.op_eq]
      · rw [e₁, e₂]) (by taint_decide)

/-- Steps that keep memory, the permissions, `ebx` and `esp` keep the body. -/
theorem Body.same {s₀ s t : State} (b : Body s₀ s) (hb : t.gpr .ebx = s.gpr .ebx)
    (he : t.gpr .esp = s.gpr .esp) (hm : t.mem = s.mem) (hrd : t.rd = s.rd) (hwr : t.wr = s.wr) :
    Body s₀ t :=
  ⟨hb.trans b.ebx, he.trans b.esp, hrd.trans b.rd, hwr.trans b.wr, hm ▸ b.frame,
    fun q hq => hm ▸ b.saved q hq, hm ▸ b.pfx⟩

/-- The body, with `L` output bytes written. -/
def OutAt (s₀ : State) (L : Nat) (s : State) : Prop :=
  Body s₀ s ∧ ∃ xs, Out s₀ s xs ∧ xs.length = L

theorem emit_blk {s₀ : State} {L : Nat} {s : State} (h : OutAt s₀ L s) :
    WP isa (.block [.mov .esi (.imm 32)]) s (CopyIn s₀ L 32) := by
  obtain ⟨b, xs, o, hx⟩ := h
  refine wp_movi fun s₁ u₁ => WP.block_nil ⟨b.same (u₁.other _ (by decide)) (u₁.other _ (by decide))
    u₁.mem u₁.rd u₁.wr, ?_, u₁.gpr⟩
  show _ = _; rw [u₁.mem, ← hx]; exact o.ptr

theorem emit_rel {s₀ s₀' : State} (hp : Pre s₀) (hp' : Pre s₀') (q : Same s₀ s₀') {L : Nat}
    (hL : L + 32 ≤ ol s₀) :
    RelCT isa (fun t₁ t₂ => OutAt s₀ L t₁ ∧ OutAt s₀' L t₂) emitPrefix fun _ _ => True := by
  have hL' : L + 32 ≤ ol s₀' := by rw [q.ol_eq]; exact hL
  have cp : ∀ {s₀ : State}, Pre s₀ → L + 32 ≤ ol s₀ → ∀ s, CopyIn s₀ L 32 s → WP isa copy s (Body s₀) :=
    fun hp hL s ⟨b, k, n⟩ => (copy_ok hp b k n (by decide) (by decide) hL).mono fun _ h => h.1
  unfold emitPrefix
  refine RelCT.seq (rel_taint [] (fun _ _ _ _ r hr => nomatch hr) ⟨_, by taint_decide⟩
    (fun _ h => emit_blk h) (fun _ h => emit_blk h))
    (RelCT.seq (rel_wp (copy_rel hp hp' q) (cp hp hL) (cp hp' hL')) ?_)
  exact RelCT.taint (A := taint) (τr [.esp, .ebx])
    (fun t₁ t₂ ⟨b₁, b₂⟩ => agree_regs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [b₁.esp, b₂.esp, q.esp]
      · rw [b₁.ebx, b₂.ebx, q.scr_eq]) (by taint_decide)

theorem rem_blk {s₀ : State} (hp : Pre s₀) {L : Nat} {s : State} (h : OutAt s₀ L s) :
    WP isa (.block [.mov .esi (.mem (VG.Impl.Sha512.X86.at_ .ebx leftOff))]) s
      (CopyIn s₀ L (ol s₀ - L)) := by
  obtain ⟨b, xs, o, hx⟩ := h
  have hs := hp.scr_fits
  refine wp_movm (VG.Proof.Sha512.X86.ea_of b.ebx leftOff)
    (by rw [b.rd, b.wr]; exact ⟨scrR s₀, by simp [hp.wr], contains_addr (by decide) (by decide) hs⟩)
    fun s₁ u₁ => WP.block_nil ⟨b.same (u₁.other _ (by decide)) (u₁.other _ (by decide))
      u₁.mem u₁.rd u₁.wr, ?_, ?_⟩
  · show _ = _; rw [u₁.mem, ← hx]; exact o.ptr
  · rw [u₁.gpr, o.left, hx]

theorem copyRemaining_rel {s₀ s₀' : State} (hp : Pre s₀) (hp' : Pre s₀') (q : Same s₀ s₀') {L : Nat} :
    RelCT isa (fun t₁ t₂ => OutAt s₀ L t₁ ∧ OutAt s₀' L t₂) copyRemaining fun _ _ => True := by
  unfold copyRemaining
  refine RelCT.seq (rel_taint [.ebx] (fun _ _ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
      rw [h₁.1.ebx, h₂.1.ebx, q.scr_eq]) ⟨_, by taint_decide⟩
    (fun _ h => rem_blk hp h) (fun _ h => rem_blk hp' h)) ?_
  rw [q.ol_eq]
  exact copy_rel hp hp' q

end VG.Proof.Argon2.X86.HPrime
