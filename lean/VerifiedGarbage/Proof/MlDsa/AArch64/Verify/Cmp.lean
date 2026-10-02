import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.Compute
import VerifiedGarbage.Proof.MlKem.AArch64.DecapsCmp

/-!
# ML-DSA verification on AArch64: the comparison of `c̃′` with `c̃`

`cmpAnd a b n` ORs the XORs of the `n` bytes at `a` and `b` into `x10`, then
ANDs `(x10 - 1) >> 63`, 1 exactly when they are equal, into `x24`
(`cmpAnd_ok`), without a branch on the bytes: its addresses and branches
depend only on the pointers (`cmp_taint`, in `Final.lean`).
-/

namespace VG.Proof.MlDsa.AArch64.Verify

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Call VG.Impl.MlDsa.AArch64.KeyGen VG.Impl.MlDsa.AArch64.Verify
open VG.Proof.MlDsa.AArch64.KeyGen
open VG.Proof.MlKem.AArch64 (Keep Only wp_ldrb wp_eor wp_orr wp_addImm wp_subImm wp_lsr wp_movz wp_nil count_loop
  ptr_add ptr_zero)
open VG.Proof.MlKem.AArch64.Decaps (xor_zero_iff bytesAt_succ')
open VG.Spec.Sha3 (bytesAt)

theorem shr_val (x : BitVec 64) (h : x.toNat < 256) : (x - 1) >>> 63 = if x = 0 then 1 else 0 := by
  by_cases hx : x = 0
  · subst hx; decide
  · rw [ite_eq_right hx]
    have h1 : 1 ≤ x.toNat := by
      rcases Nat.eq_zero_or_pos x.toNat with h0 | h0
      · exact absurd (BitVec.eq_of_toNat_eq (by rw [h0]; rfl)) hx
      · exact h0
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub_of_le (by
      show (1 : BitVec 64).toNat ≤ x.toNat; exact h1)]
    show (x.toNat - 1) >>> 63 = 0
    rw [Nat.shiftRight_eq_div_pow]
    omega

/-- After `k` of the `n` bytes at `A` and `B`. -/
structure CI (A B : Addr) (n : Nat) (s : State) (k : Nat) (u : State) : Prop where
  keep : Keep [.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11] s u
  mem : u.mem = s.mem
  x0 : u.gpr .x0 = A + BitVec.ofNat 64 k
  x1 : u.gpr .x1 = B + BitVec.ofNat 64 k
  x2 : (u.gpr .x2).toNat = n - k
  x10 : (u.gpr .x10).toNat < 256
  eq : u.gpr .x10 = 0 ↔ bytesAt s.mem A k = bytesAt s.mem B k

theorem cstep {A B : Addr} {n : Nat} {s : State} (hn : n < 2 ^ 32)
    (ha : InRegions (s.rd ++ s.wr) A n) (hb : InRegions (s.rd ++ s.wr) B n) {k : Nat} (hk : k < n)
    {u : State} (h : CI A B n s k u) :
    WP isa (.block cmpBody) u fun u' => CI A B n s (k + 1) u' ∧ ((u'.gpr .x2).toNat ≠ 0 ↔ k + 1 ≠ n) := by
  have in₁ : InRegions (u.rd ++ u.wr) (A + BitVec.ofNat 64 k) 1 := by
    rw [h.keep.rd, h.keep.wr]; exact inRegions_sub ha (by omega) (by omega)
  have in₂ : InRegions (u.rd ++ u.wr) (B + BitVec.ofNat 64 k) 1 := by
    rw [h.keep.rd, h.keep.wr]; exact inRegions_sub hb (by omega) (by omega)
  refine wp_ldrb (a := A + BitVec.ofNat 64 k) (by decide) (by rw [h.x0, ptr_zero]) in₁ fun u₁ g₁ v₁ => ?_
  refine wp_ldrb (a := B + BitVec.ofNat 64 k) (by decide) (by rw [g₁.get .x1, h.x1, ptr_zero])
    (by rw [g₁.rd, g₁.wr]; exact in₂) fun u₂ g₂ v₂ => ?_
  refine wp_eor fun u₃ g₃ v₃ => wp_orr fun u₄ g₄ v₄ => wp_addImm (by decide) fun u₅ g₅ v₅ =>
    wp_addImm (by decide) fun u₆ g₆ v₆ => wp_subImm (by decide) fun u₇ g₇ v₇ => wp_nil ?_
  have o₇ : Only [.x0, .x1, .x2, .x9, .x10, .x11] u u₇ :=
    ((((((g₁.trans g₂).trans g₃).trans g₄).trans g₅).trans g₆).trans g₇).mono
  have m₁ : u₁.mem = s.mem := by rw [g₁.mem, h.mem]
  have x9 : u₃.gpr .x9 = (s.mem (A + BitVec.ofNat 64 k)).setWidth 64 ^^^
      (s.mem (B + BitVec.ofNat 64 k)).setWidth 64 := by
    rw [v₃, g₂.get .x9, v₁, v₂, m₁, h.mem]
  have x10 : u₇.gpr .x10 = u.gpr .x10 ||| u₃.gpr .x9 := by
    rw [g₇.get .x10, g₆.get .x10, g₅.get .x10, v₄, g₃.get .x10, g₂.get .x10, g₁.get .x10]
  have x2 : u₇.gpr .x2 = u.gpr .x2 - BitVec.ofNat 64 1 := by
    rw [v₇, g₆.get .x2, g₅.get .x2, g₄.get .x2, g₃.get .x2, g₂.get .x2, g₁.get .x2]
  have hx2 : (u₇.gpr .x2).toNat = n - (k + 1) := by
    rw [x2, BitVec.toNat_sub_of_le (show (BitVec.ofNat 64 1).toNat ≤ (u.gpr .x2).toNat by
      rw [h.x2, BitVec.toNat_ofNat]; omega), h.x2, BitVec.toNat_ofNat]
    omega
  refine ⟨⟨h.keep.trans o₇.keep |>.mono, by rw [o₇.mem, h.mem], ?_, ?_, hx2, ?_, ?_⟩, by rw [hx2]; omega⟩
  · rw [g₇.get .x0, g₆.get .x0, v₅, g₄.get .x0, g₃.get .x0, g₂.get .x0, g₁.get .x0, h.x0, ptr_add]
  · rw [g₇.get .x1, v₆, g₅.get .x1, g₄.get .x1, g₃.get .x1, g₂.get .x1, g₁.get .x1, h.x1, ptr_add]
  · rw [x10, BitVec.toNat_or, x9, BitVec.toNat_xor, BitVec.toNat_setWidth, BitVec.toNat_setWidth]
    have a := (s.mem (A + BitVec.ofNat 64 k)).isLt
    have b := (s.mem (B + BitVec.ofNat 64 k)).isLt
    have c := h.x10
    exact Nat.or_lt_two_pow (n := 8) c (Nat.xor_lt_two_pow (by omega) (by omega))
  · have e1 : u.gpr .x10 ||| u₃.gpr .x9 = 0 ↔ u.gpr .x10 = 0 ∧ u₃.gpr .x9 = 0 := BitVec.or_eq_zero_iff
    rw [x10, e1, h.eq, x9, xor_zero_iff, bytesAt_succ', bytesAt_succ']
    constructor
    · rintro ⟨h1, h2⟩; rw [h1, h2]
    · intro e
      obtain ⟨h1, h2⟩ := List.append_inj e (by rw [Proof.MlKem.bytesAt_length, Proof.MlKem.bytesAt_length])
      exact ⟨h1, List.head_eq_of_cons_eq h2⟩

theorem cmpAnd_ok {S : Nat} {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay S rbs wbs s) {a b : Ptr} {n : Nat}
    (hn : 0 < n) (hn' : n < 65536) (ha : inB (rbs ++ wbs) a n = true) (hb : inB (rbs ++ wbs) b n = true) :
    WP isa (cmpAnd a b n) s fun s' => PPostB S s s' [] ∧
      s'.gpr .x24 = ((s.gpr .x24).setWidth 32 &&&
        (if bytesAt s.mem (pa s a) n = bytesAt s.mem (pa s b) n then (1 : BitVec 64) else 0).setWidth 32).setWidth 64 := by
  have hA := L.inR ha
  have hB := L.inR hb
  have hok : ∀ x ∈ [(Reg.x0, Arg.ptr a), (.x1, .ptr b), (.x2, .imm n)], x.2.Ok ∧ x.1 ∈ argRegs := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro x (rfl | rfl | rfl)
    exacts [⟨ptr_ok (L.ptrBs ha), .inl rfl⟩, ⟨ptr_ok (L.ptrBs hb), .inr (.inl rfl)⟩, ⟨trivial, .inr (.inr (.inl rfl))⟩]
  unfold cmpAnd
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (glue_ok hok (by simp only [List.map_cons, List.map_nil]; decide) s) fun s₁ h₁ => wp_movz fun s₂ h₂ e₂ => wp_nil ?_
  have a0 := Args.r0 h₁; have a1 := Args.r1 h₁; have a2 := Args.r2 h₁
  have k₂ : Keep [.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11] s s₂ :=
    (h₁.2.trans h₂.keep).mono (by decide)
  have c₀ : CI (pa s a) (pa s b) n s 0 s₂ :=
    ⟨k₂, by rw [h₂.mem, h₁.1.2], by rw [h₂.get .x0, a0, ptr_zero]; rfl, by rw [h₂.get .x1, a1, ptr_zero]; rfl,
      by rw [h₂.get .x2, a2]; simp only [Arg.val, BitVec.toNat_ofNat]; omega, by rw [e₂]; decide,
      by rw [e₂]; exact ⟨fun _ => rfl, fun _ => rfl⟩⟩
  refine WP.seq (WP.mono (count_loop (cr := .x2) hn (CI (pa s a) (pa s b) n s)
    (fun k hk u h => cstep (by omega) hA hB hk h) c₀) fun s₃ h₃ => ?_)
  refine wp_subImm (by decide) fun s₄ h₄ e₄ => wp_lsr (by decide) fun s₅ h₅ e₅ =>
    wp_and32 fun s₆ h₆ e₆ => wp_nil ?_
  have o₆ : Only [.x10, .x24] s₃ s₆ := ((h₄.trans h₅).trans h₆).mono
  have k₆ : Keep [.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x24] s s₆ :=
    (h₃.keep.trans o₆.keep).mono (by decide)
  refine ⟨postB_of_keep k₆ (by decide) (by rw [o₆.mem, h₃.mem]; exact Frame.refl _ _), ?_⟩
  have x24 : s₅.gpr .x24 = s.gpr .x24 := by
    rw [h₅.get .x24 (by decide), h₄.get .x24 (by decide), h₃.keep.gpr .x24 (by decide)]
  have x10 : s₅.gpr .x10 = (s₃.gpr .x10 - 1) >>> 63 := by rw [e₅, e₄]; rfl
  rw [e₆, x24, x10, shr_val _ h₃.x10]
  have he := h₃.eq
  by_cases e : bytesAt s.mem (pa s a) n = bytesAt s.mem (pa s b) n
  · rw [ite_eq_left (he.mpr e), ite_eq_left e]
  · rw [ite_eq_right (fun h => e (he.mp h)), ite_eq_right e]

end VG.Proof.MlDsa.AArch64.Verify
