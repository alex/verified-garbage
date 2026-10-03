import VerifiedGarbage.Proof.Argon2.X86.HPrime.Calls

/-!
# Argon2 H′ on x86 (32-bit): hashing in `scratch`

What the hash macros keep (`Keeps`: `ebx`, `ebp`, `esp`, the permissions, and
the memory outside `scratch[0, 832)` and the stack below `esp`), and the hash of
a fixed `scratch` buffer (`absorbFixed_ok`) and of the 64-byte digest
(`next_ok`).
-/

namespace VG.Proof.Argon2.X86.HPrime

open VG VG.X86 VG.Spec.Blake2
open VG.Impl.Argon2.X86.HPrime (init update finalize absorbFixed next)
open VG.Proof.Sha256.X86.Stream (Upd wp_movi wp_mov wp_addi)

/-- What the hash macros keep. -/
structure Keeps (B E : BitVec 32) (s t : State) : Prop where
  ebx : t.gpr .ebx = s.gpr .ebx
  ebp : t.gpr .ebp = s.gpr .ebp
  esp : t.gpr .esp = s.gpr .esp
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [⟨B.setWidth 64, 832⟩, below E 60] s.mem t.mem

theorem Keeps.refl {B E : BitVec 32} (s : State) : Keeps B E s s :=
  ⟨rfl, rfl, rfl, rfl, rfl, Frame.refl _ _⟩

theorem Keeps.trans {B E : BitVec 32} {s t u : State} (h : Keeps B E s t) (h' : Keeps B E t u) :
    Keeps B E s u :=
  ⟨h'.ebx.trans h.ebx, h'.ebp.trans h.ebp, h'.esp.trans h.esp, h'.rd.trans h.rd, h'.wr.trans h.wr,
    h.frame.trans h'.frame⟩

theorem Keeps.ctx {B E : BitVec 32} {s t : State} (h : Keeps B E s t) (c : Ctx B E s) : Ctx B E t :=
  c.of_regs h.ebx h.esp h.wr

/-- Calls keep the callee-saved registers and write within the regions. -/
theorem Keeps.of_call {B E : BitVec 32} {s t : State} (hr : ∀ r ∈ [Reg.ebx, .ebp, .esp], t.gpr r = s.gpr r)
    (hrd : t.rd = s.rd) (hwr : t.wr = s.wr) {rs : List Region} (hf : Frame rs s.mem t.mem)
    (hs : ∀ r ∈ rs, ∃ r' ∈ [(⟨B.setWidth 64, 832⟩ : Region), below E 60], Region.Sub r r') :
    Keeps B E s t :=
  ⟨hr _ (by simp), hr _ (by simp), hr _ (by simp), hrd, hwr, hf.sub hs⟩

/-- The registers `Keeps` asks for are callee-saved. -/
theorem of_callee {s t : State} (h : ∀ r ∈ calleeSaved, t.gpr r = s.gpr r) :
    ∀ r ∈ [Reg.ebx, .ebp, .esp], t.gpr r = s.gpr r :=
  fun r hr => h r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> decide)

/-- Bytes outside `scratch[0, 832)` and the stack are kept. -/
theorem Keeps.bytes {B E : BitVec 32} {s t : State} (h : Keeps B E s t) {R : Region}
    (hR : R.len ≤ 2 ^ 64) (h₁ : R.Disjoint ⟨B.setWidth 64, 832⟩) (h₂ : R.Disjoint (below E 60)) :
    bytesAt t.mem R.base R.len = bytesAt s.mem R.base R.len :=
  Proof.Blake2.bytesAt_congr fun i hi => h.frame.bytes (R := R) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h₁
    · exact h₂) hR hi

/-! ## Fixed buffers -/

/-- Absorb `size` bytes at `scratch + offset` into an empty state. -/
theorem absorbFixed_ok {B E : BitVec 32} {s : State} (c : Ctx B E s) {offset size : Nat}
    (ho : B.toNat + offset + size ≤ 2 ^ 32) (hlo : 768 ≤ offset) (hs : 0 < size)
    (hcov : Covers [⟨B.setWidth 64 + BitVec.ofNat 64 offset, size⟩] s.wr)
    (hstk : (below E 60).Disjoint ⟨B.setWidth 64 + BitVec.ofNat 64 offset, size⟩) {h0 : HashValue 64}
    (repr : Repr b h0 s.mem (B.setWidth 64) []) :
    WP isa (absorbFixed offset size) s fun t =>
      Repr b h0 t.mem (B.setWidth 64) (bytesAt s.mem (B.setWidth 64 + BitVec.ofNat 64 offset) size) ∧
      Keeps B E s t := by
  unfold absorbFixed
  have hfit := c.fits
  refine WP.seq (wp_movi fun s₁ u₁ => wp_movi fun s₂ u₂ => wp_mov fun s₃ u₃ => wp_addi fun s₄ u₄ =>
    wp_movi fun s₅ u₅ => WP.block_nil ?_)
  have o : ∀ r, r ≠ .ecx → r ≠ .edx → r ≠ .esi → r ≠ .edi → s₅.gpr r = s.gpr r := fun r h1 h2 h3 h4 => by
    rw [u₅.other _ h4, u₄.other _ h3, u₃.other _ h3, u₂.other _ h2, u₁.other _ h1]
  have m : s₅.mem = s.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have c₅ : Ctx B E s₅ := c.of_regs (o _ (by decide) (by decide) (by decide) (by decide))
    (o _ (by decide) (by decide) (by decide) (by decide)) (by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr])
  have eD : s₅.gpr .esi = B + BitVec.ofNat 32 offset := by
    rw [u₅.other _ (by decide), u₄.gpr, u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), c.ebx]
  have eDw : (B + BitVec.ofNat 32 offset).setWidth 64 = B.setWidth 64 + BitVec.ofNat 64 offset :=
    setWidth_add (by omega)
  have dTo : (B + BitVec.ofNat 32 offset).toNat = B.toNat + offset := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := offset) (by omega)]; omega
  have hL : (s₅.gpr .edi).toNat = size := by
    rw [u₅.gpr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hDc : Covers [⟨(B + BitVec.ofNat 32 offset).setWidth 64, size⟩] (s₅.rd ++ s₅.wr) := by
    rw [eDw, show s₅.wr = s.wr by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]]; exact Covers.right hcov
  have hDs : Region.Disjoint ⟨(B + BitVec.ofNat 32 offset).setWidth 64, size⟩ ⟨B.setWidth 64, 768⟩ := by
    rw [eDw]; exact Offset.disjoint_base _ hlo (by omega)
  have hDk : (below E 60).Disjoint ⟨(B + BitVec.ofNat 32 offset).setWidth 64, size⟩ := by
    rw [eDw]; exact hstk
  have hcount : s₅.gpr .edx ++ s₅.gpr .ecx = BitVec.ofNat 64 ([] : List Byte).length := by
    have e1 : s₅.gpr .edx = 0 := by
      rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr]
    have e2 : s₅.gpr .ecx = 0 := by
      rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
        u₂.other _ (by decide), u₁.gpr]
    rw [e1, e2]; rfl
  refine (update_ok c₅ eD hL (by rw [dTo]; omega) hDc hDs hDk (by rw [m]; exact repr) hcount
    (by simp only [List.length_nil]; omega)).mono ?_
  rintro t ⟨r, cs, rd, wr, f⟩
  refine ⟨by rw [m, eDw, List.nil_append] at r; exact r, ?_⟩
  refine Keeps.of_call (fun q hq => (of_callee cs q hq).trans ?_) (rd.trans ?_) (wr.trans ?_) (m ▸ f) ?_
  · have : q ≠ .ecx ∧ q ≠ .edx ∧ q ≠ .esi ∧ q ≠ .edi := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl <;> decide
    exact o q this.1 this.2.1 this.2.2.1 this.2.2.2
  · rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self, Region.sub_prefix (by decide)⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩

end VG.Proof.Argon2.X86.HPrime
