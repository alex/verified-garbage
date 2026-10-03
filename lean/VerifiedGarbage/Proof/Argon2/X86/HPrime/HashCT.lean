import VerifiedGarbage.Proof.Argon2.X86.HPrime.Next
import VerifiedGarbage.Proof.Argon2.X86.HPrime.CallsCT

/-!
# Argon2 H′ on x86 (32-bit): the hash macros, in two runs

`absorbFixed_rel` and `next_rel`: hashing a fixed buffer of `scratch`, and
the digest, leak the same trace in two runs with the same `scratch` and
stack pointer.
-/

namespace VG.Proof.Argon2.X86.HPrime

open VG VG.X86 VG.Spec.Blake2
open VG.Impl.Argon2.X86.HPrime (init update finalize absorbFixed next)
open VG.Proof.Sha256.X86.Stream (Upd wp_movi wp_mov wp_addi)

/-- The instructions before `absorbFixed`'s call of `update`. -/
theorem absorbFixed_blk {B E : BitVec 32} {s : State} (c : Ctx B E s) {offset size : Nat}
    (ho : B.toNat + offset + size ≤ 2 ^ 32) (hs : 0 < size) (hlt : size < 2 ^ 32)
    (hcov : Covers [⟨B.setWidth 64 + BitVec.ofNat 64 offset, size⟩] s.wr) :
    WP isa (.block [.mov .ecx (.imm 0), .mov .edx (.imm 0), .mov .esi (.reg .ebx),
      .alu .add .esi (.imm (BitVec.ofNat 32 offset)), .mov .edi (.imm (BitVec.ofNat 32 size))]) s
      (UpdateIn B E (B + BitVec.ofNat 32 offset) size 0 0) := by
  have hfit := c.fits
  refine wp_movi fun s₁ u₁ => wp_movi fun s₂ u₂ => wp_mov fun s₃ u₃ => wp_addi fun s₄ u₄ =>
    wp_movi fun s₅ u₅ => WP.block_nil ?_
  have o : ∀ r, r ≠ .ecx → r ≠ .edx → r ≠ .esi → r ≠ .edi → s₅.gpr r = s.gpr r := fun r h1 h2 h3 h4 => by
    rw [u₅.other _ h4, u₄.other _ h3, u₃.other _ h3, u₂.other _ h2, u₁.other _ h1]
  have w : s₅.wr = s.wr := by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  refine ⟨c.of_regs (o _ (by decide) (by decide) (by decide) (by decide))
    (o _ (by decide) (by decide) (by decide) (by decide)) w, ?_, ?_, ?_, ?_, ?_⟩
  · rw [u₅.other _ (by decide), u₄.gpr, u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), c.ebx]
  · rw [u₅.gpr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.gpr]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr]
  · rw [setWidth_add (by omega), show s₅.rd ++ s₅.wr = s.rd ++ s.wr by
      rw [w, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]]
    exact Covers.right hcov

/-- What `absorbFixed` needs: the context, and the buffer writable. -/
def FixedIn (B E : BitVec 32) (offset size : Nat) (s : State) : Prop :=
  Ctx B E s ∧ Covers [⟨B.setWidth 64 + BitVec.ofNat 64 offset, size⟩] s.wr

theorem absorbFixed_rel {B E : BitVec 32} {offset size : Nat} (ho : B.toNat + offset + size ≤ 2 ^ 32)
    (hlo : 768 ≤ offset) (hs : 0 < size)
    (hstk : (below E 60).Disjoint ⟨B.setWidth 64 + BitVec.ofNat 64 offset, size⟩)
    (hc : ∃ hc, (VG.Taint.check taint (τr [.esp, .ebx]) (.block [.mov .ecx (.imm 0), .mov .edx (.imm 0),
      .mov .esi (.reg .ebx), .alu .add .esi (.imm (BitVec.ofNat 32 offset)),
      .mov .edi (.imm (BitVec.ofNat 32 size))]) hc).isSome = true) :
    RelCT isa (fun s₁ s₂ => FixedIn B E offset size s₁ ∧ FixedIn B E offset size s₂)
      (absorbFixed offset size) fun _ _ => True := by
  have eD : (B + BitVec.ofNat 32 offset).setWidth 64 = B.setWidth 64 + BitVec.ofNat 64 offset :=
    setWidth_add (by omega)
  have dTo : (B + BitVec.ofNat 32 offset).toNat = B.toNat + offset := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := offset) (by omega)]; omega
  unfold absorbFixed
  refine RelCT.seq (rel_taint [.esp, .ebx] (fun s₁ s₂ ⟨c₁, _⟩ ⟨c₂, _⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [c₁.esp, c₂.esp]
      · rw [c₁.ebx, c₂.ebx]) hc
    (fun s ⟨c, h⟩ => absorbFixed_blk c ho hs (by omega) h) (fun s ⟨c, h⟩ => absorbFixed_blk c ho hs (by omega) h))
    (update_rel (by rw [dTo]; omega) (by rw [eD]; exact Offset.disjoint_base _ hlo (by omega))
      (by rw [eD]; exact hstk))

/-- The instructions before `absorbFixed`'s call, from `esp` and `ebx` public. -/
abbrev FixedCheck (offset size : Nat) : Prop :=
  ∃ hc, (VG.Taint.check taint (τr [.esp, .ebx]) (.block [.mov .ecx (.imm 0), .mov .edx (.imm 0),
      .mov .esi (.reg .ebx), .alu .add .esi (.imm (BitVec.ofNat 32 offset)),
      .mov .edi (.imm (BitVec.ofNat 32 size))]) hc).isSome = true

theorem fixed_check_768 : FixedCheck 768 64 := ⟨_, by taint_decide⟩
theorem fixed_check_832 : FixedCheck 832 4 := ⟨_, by taint_decide⟩

/-- `next`, from the context and the digest length in `edx`. -/
theorem next_rel {B E : BitVec 32} {n : Nat} (hn₁ : 1 ≤ n) (hn₂ : n ≤ 64) :
    RelCT isa (fun s₁ s₂ => InitIn B E n s₁ ∧ InitIn B E n s₂) next fun _ _ => True := by
  have st : ∀ s, InitIn B E n s → WP isa init s fun t =>
      Repr b (Spec.Blake2.init b n 0) t.mem (B.setWidth 64) [] ∧ Ctx B E t := fun s ⟨c, e⟩ =>
    (init_ok c e hn₁ hn₂).mono fun t ⟨r, cs, _, wr, _⟩ =>
      ⟨r, c.of_regs (cs _ (by decide)) (cs _ (by decide)) wr⟩
  have fx : ∀ s, Repr b (Spec.Blake2.init b n 0) s.mem (B.setWidth 64) [] ∧ Ctx B E s →
      WP isa (absorbFixed 768 64) s fun t => Ctx B E t := fun s ⟨r, c⟩ =>
    (absorbFixed_ok c (offset := 768) (size := 64) (by have := c.fits; omega) (by decide) (by decide)
      (c.cov (by decide)) (c.stk_sub (by decide) (by decide)) r).mono fun t ⟨_, k⟩ => k.ctx c
  have fin : ∀ s, Ctx B E s → WP isa (.block [.mov .ecx (.imm 64), .mov .edx (.imm 0)]) s
      (FinalizeIn B E 64 0) := fun s c =>
    wp_movi fun s₁ u₁ => wp_movi fun s₂ u₂ => WP.block_nil
      ⟨c.of_regs (by rw [u₂.other _ (by decide), u₁.other _ (by decide)])
        (by rw [u₂.other _ (by decide), u₁.other _ (by decide)]) (by rw [u₂.wr, u₁.wr]),
       by rw [u₂.other _ (by decide), u₁.gpr], u₂.gpr⟩
  unfold next
  refine RelCT.seq (rel_wp (init_rel hn₁ hn₂) st st)
    (RelCT.seq (R := fun s₁ s₂ => Ctx B E s₁ ∧ Ctx B E s₂) ?_
      (RelCT.seq (R := fun s₁ s₂ => FinalizeIn B E 64 0 s₁ ∧ FinalizeIn B E 64 0 s₂) ?_ finalize_rel))
  · refine rel_wp (RelCT.of_pre fun s₁ _ ⟨⟨_, c₁⟩, _⟩ =>
      (absorbFixed_rel (B := B) (E := E) (offset := 768) (size := 64) (by have := c₁.fits; omega)
        (by decide) (by decide) (c₁.stk_sub (by decide) (by decide)) fixed_check_768).mono
      (fun s₁ s₂ ⟨⟨_, c₁⟩, ⟨_, c₂⟩⟩ => ⟨⟨c₁, c₁.cov (by decide)⟩, ⟨c₂, c₂.cov (by decide)⟩⟩)
      fun _ _ h => h) fx fx
  · exact rel_taint [.esp, .ebx] (fun s₁ s₂ c₁ c₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [c₁.esp, c₂.esp]
      · rw [c₁.ebx, c₂.ebx]) ⟨_, by taint_decide⟩ fin fin

end VG.Proof.Argon2.X86.HPrime
