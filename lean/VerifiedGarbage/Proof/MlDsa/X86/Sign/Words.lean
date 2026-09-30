import VerifiedGarbage.Proof.MlDsa.X86.Sign.Inv

/-!
# ML-DSA signing on x86 (32-bit): words and bytes of `scratch`

Untrusted: everything here is checked by Lean. The small blocks between
calls, as what they leave in `scratch` and the frame of what they change:
a word or a byte set (`wp_st32`, `wp_st8`), `OK ← OK ∧ eax` (`wp_andOK`)
and `ONES ← ONES + eax` (`wp_addOnes`).
-/

namespace VG.Proof.MlDsa.X86.Sign

open VG VG.X86
open VG.Impl.MlKem.X86 (Buf at_)
open VG.Impl.MlDsa.X86.Sign
open VG.Proof.MlKem.X86 (Only wp_cons)
open VG.Proof.MlKem.X86.Top
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

variable {p : Params}

theorem sc_ok (ps : PS p) {o n : Nat} (h : o + n ≤ 5120) (hn : 0 < n) : (Y p).okW (sc o n) = true := by ofs

theorem sc_ok' (ps : PS p) {o n : Nat} (h : o + n ≤ 5120) (hn : 0 < n) : (Y p).ok (sc o n) = true :=
  (Lay.okW_iff.mp (sc_ok ps h hn)).1

/-- The address of a part of a buffer. -/
theorem addr_off {Y : Lay} {s₀ : State} (hp : TPre Y s₀) {a o d l l' : Nat} (h₁ : Y.ok ⟨a, o, l⟩ = true)
    (h₂ : Y.ok ⟨a, o + d, l'⟩ = true) : Buf.addr s₀ ⟨a, o + d, l'⟩ = Buf.addr s₀ ⟨a, o, l⟩ + BitVec.ofNat 64 d := by
  rw [Buf.addr_eq hp h₂, Buf.addr_eq hp h₁, BitVec.add_assoc, ← BitVec.ofNat_add]

theorem bytes1_write (m : Mem) (a : Addr) (v : Byte) : bytesAt (m.writeW a v) a 1 = [v] := by
  simp only [bytesAt, List.range_one, List.map_cons, List.map_nil, BitVec.add_zero,
    VG.Proof.MlKem.writeW8_apply, ite_true]

theorem setWidth8_ofNat (v : Nat) : (BitVec.ofNat 32 v).setWidth 8 = BitVec.ofNat 8 v := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  exact Nat.mod_mod_of_dvd v (by decide)

theorem and01 (a b : Bool) :
    ((if a then 1 else 0 : BitVec 32) &&& (if b then 1 else 0)) = if a && b then 1 else 0 := by
  cases a <;> cases b <;> rfl

section
variable {s₀ s : State} (hp : TPre (Y p) s₀) (h : Ctx (Y p) s₀ s)
include hp h

/-- The word at `o` set to `v`. -/
theorem wp_st32 {o : Nat} (hc : (Y p).okW (sc o 4) = true) (v : Nat) {is : List Instr} {Q : State → Prop}
    (k : ∀ s', Ctx (Y p) s₀ s' → Frame (FR s₀ [sc o 4] 0) s.mem s'.mem → scw s₀ s' o = BitVec.ofNat 32 v →
      WP isa (.block is) s' Q) :
    WP isa (.block (st32 o v ++ is)) s Q := by
  simp only [st32, List.cons_append, List.nil_append]
  refine wp_movi fun s₁ o₁ v₁ => ?_
  refine wp_stsc hp (h.only o₁ (by simp) (by simp)) hc fun s₂ c₂ g₂ m₂ => k s₂ c₂ ?_ ?_
  · rw [m₂, o₁.mem]; exact frW32 (Y := Y p)
  · rw [scw, m₂, Mem.readW_writeW_self32, v₁]

/-- The byte at `o` set to `v`. -/
theorem wp_st8 {o : Nat} (hc : (Y p).okW (sc o 1) = true) (v : Nat) {is : List Instr} {Q : State → Prop}
    (k : ∀ s', Ctx (Y p) s₀ s' → Frame (FR s₀ [sc o 1] 0) s.mem s'.mem →
      bytesAt s'.mem (Buf.addr s₀ (sc o 1)) 1 = [BitVec.ofNat 8 v] → WP isa (.block is) s' Q) :
    WP isa (.block (st8 o v ++ is)) s Q := by
  simp only [st8, List.cons_append, List.nil_append]
  refine wp_movi fun s₁ o₁ v₁ => ?_
  refine wp_st8sc hp (h.only o₁ (by simp) (by simp)) hc fun s₂ c₂ g₂ m₂ => k s₂ c₂ ?_ ?_
  · rw [m₂, o₁.mem]; exact frW8 (Y := Y p)
  · rw [m₂, bytes1_write]; show [(s₁.gpr .eax).setWidth 8] = _; rw [v₁, setWidth8_ofNat]

/-- `OK ← OK ∧ eax`. -/
theorem wp_andOK (ps : PS p) {Q : State → Prop}
    (k : ∀ s', Ctx (Y p) s₀ s' → Frame (FR s₀ [sc oOK 4] 0) s.mem s'.mem →
      scw s₀ s' oOK = scw s₀ s oOK &&& s.gpr .eax → Q s') :
    WP isa (.block andOK) s Q := by
  unfold andOK
  refine wp_ldsc hp h (sc_ok' ps (by decide) (by decide)) fun s₁ o₁ v₁ => wp_andr fun s₂ o₂ v₂ => ?_
  have o := o₁.trans o₂
  refine wp_stsc hp (h.only o (by simp) (by simp)) (sc_ok ps (by decide) (by decide)) fun s₃ c₃ g₃ m₃ =>
    WP.block_nil_iff.mpr (k s₃ c₃ ?_ ?_)
  · rw [m₃, o.mem]; exact frW32 (Y := Y p)
  · rw [scw, m₃, Mem.readW_writeW_self32, v₂, v₁, o₁.gpr .eax (by simp)]

/-- `ONES ← ONES + eax`. -/
theorem wp_addOnes (ps : PS p) {Q : State → Prop}
    (k : ∀ s', Ctx (Y p) s₀ s' → Frame (FR s₀ [sc oONES 4] 0) s.mem s'.mem →
      scw s₀ s' oONES = scw s₀ s oONES + s.gpr .eax → Q s') :
    WP isa (.block addOnes) s Q := by
  unfold addOnes
  refine wp_ldsc hp h (sc_ok' ps (by decide) (by decide)) fun s₁ o₁ v₁ => wp_addr fun s₂ o₂ v₂ => ?_
  have o := o₁.trans o₂
  refine wp_stsc hp (h.only o (by simp) (by simp)) (sc_ok ps (by decide) (by decide)) fun s₃ c₃ g₃ m₃ =>
    WP.block_nil_iff.mpr (k s₃ c₃ ?_ ?_)
  · rw [m₃, o.mem]; exact frW32 (Y := Y p)
  · rw [scw, m₃, Mem.readW_writeW_self32, v₂, v₁, o₁.gpr .eax (by simp)]

end

/-! ## Frames of the small blocks -/

theorem fr0 {s₀ : State} (hp : TPre (Y p) s₀) {bs : List Buf} {N : Nat} (hN : N ≤ 80) {m m' : Mem}
    (fr : Frame (FR s₀ bs 0) m m') : Frame (FR s₀ bs N) m m' :=
  fr.sub fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
    · rw [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _),
        stk_sub hp (Nat.zero_le N) (by show N + 16 ≤ 96; omega)⟩

theorem scr_ge (ps : PS p) : oP (nS p) ≤ scrLen p := by ofs

/-- The frame of a piece that writes only in `scratch[lo : hi]`, as that buffer. -/
theorem frSc {s₀ : State} (hp : TPre (Y p) s₀) {bs : List Buf} {N M : Nat} (hNM : N ≤ M) (hM : M ≤ 80)
    {lo hi : Nat} (hlh : lo < hi) (hhi : hi ≤ scrLen p)
    (h : ∀ c ∈ bs, c.arg = SC ∧ lo ≤ c.off ∧ c.off + c.len ≤ hi ∧ 0 < c.len) {m m' : Mem}
    (fr : Frame (FR s₀ bs N) m m') : Frame (FR s₀ [sc lo (hi - lo)] M) m m' :=
  frIn hp hNM hM (fun c hc => by
    obtain ⟨h₁, h₂, h₃, h₄⟩ := h c hc
    refine ⟨Lay.ok_iff.mpr ⟨by rw [h₁, Y_n]; decide, h₄, by rw [h₁, Y_alen4]; omega⟩, _, List.mem_singleton_self _,
      Lay.ok_iff.mpr ⟨by rw [Y_n]; exact (by decide : 4 < 5), by simp only; omega, by rw [Y_alen4]; simp only; omega⟩, h₁, by simp only; omega,
      by simp only; omega⟩) fr

/-- `keepB`, for bytes of `scratch` that may be none. -/
theorem keepB0 {s₀ : State} (hp : TPre (Y p) s₀) {bs : List Buf} {N : Nat} (hN : N ≤ 80)
    {m m' : Mem} (fr : Frame (FR s₀ bs N) m m') {o l : Nat} (L : Nat) (hl : o + l ≤ scrLen p)
    (h : ∀ c ∈ bs, Out p o (o + l) c) : bytesAt m' (Buf.addr s₀ (sc o L)) l = bytesAt m (Buf.addr s₀ (sc o L)) l := by
  rcases Nat.eq_zero_or_pos l with rfl | hl0
  · rfl
  · exact keepB hp hN fr (l := l) (Lay.ok_iff.mpr ⟨by rw [Y_n]; exact (by decide : 4 < 5), hl0, by rw [Y_alen4]; exact hl⟩) h

end VG.Proof.MlDsa.X86.Sign
