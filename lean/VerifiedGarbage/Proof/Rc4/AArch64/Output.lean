import VerifiedGarbage.Proof.Rc4.AArch64.Step

/-!
# A keystream byte

`output_ok`: with the output index `X` (from the base) broadcast in `v6`,
the keystream byte `S[X]` is looked up and XORed into the data byte at `x1`;
`x1` and `x2` advance.
-/

namespace VG.Proof.Rc4.AArch64
open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Rc4.AArch64

theorem low_byte (K : BitVec 8) : ((bc K).extractLsb' 0 32).setWidth 8 = K := by
  have h := vbyte_bc K (e := 0) (by decide)
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have := congrArg (·.getLsbD i) h
  simp only [vbyte, BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and, Nat.mul_zero,
    Nat.zero_add] at this
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and,
    show i < 32 by omega, Nat.zero_add]
  exact this

theorem xor_low_byte (a : BitVec 8) (w : BitVec 32) :
    ((a.setWidth 32 ^^^ w).setWidth 8) = a ^^^ w.setWidth 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp [hi, show i < 32 by omega]

/-- The scalar part: the byte's XOR, and the pointer and count. -/
theorem outScalar_ok {s : State} {K : BitVec 8} (h7 : s.v .v7 = bc K)
    (hd : InRegions s.wr (s.gpr .x1) 1) :
    WP isa (.block [.umov .w .x6 .v7 0, .ldrb .x7 .x1 0, .logic .eor .w .x7 .x7 .x6, .strb .x7 .x1 0,
        .addImm .x .x1 .x1 1, .subImm .x .x2 .x2 1]) s fun t =>
      t.mem = s.mem.write (s.gpr .x1) 1 (s.mem (s.gpr .x1) ^^^ K) ∧
      t.gpr .x1 = s.gpr .x1 + 1 ∧ t.gpr .x2 = s.gpr .x2 - 1 ∧
      (∀ r, r ≠ .x1 → r ≠ .x2 → r ≠ .x6 → r ≠ .x7 → t.gpr r = s.gpr r) ∧
      t.v = s.v ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  have hr : InRegions (s.rd ++ s.wr) (s.gpr .x1) 1 := by
    obtain ⟨region, hregion, hc⟩ := hd
    exact ⟨region, List.mem_append_right _ hregion, hc⟩
  have hc8 (x : BitVec 32) : (x.setWidth 64).setWidth 32 = x :=
    (BitVec.setWidth_setWidth_of_le x (by decide)).trans (BitVec.setWidth_eq x)
  have read1 (m : Mem) (p : Addr) : m.read p 1 = m p := by
    change (0#0 ++ m p : BitVec 8) = m p
    exact BitVec.zero_width_append _ _
  rrun [State.store, hd, hr, read1, hc8, h7, xor_low_byte, low_byte]
  refine ⟨fun r h1 h2 h6 h7 => by simp [h1, h2, h6, h7], ?_⟩
  simp [State.write]

/-- The registers the output changes. -/
def outRegs : List VReg := [.v1, .v2, .v3, .v7]

theorem output_ok {s : State} (hk : Consts s) {X : BitVec 8} (hx : s.v .v6 = bc X)
    (hd : InRegions s.wr (s.gpr .x1) 1) :
    WP isa (.block output) s fun t =>
      t.mem = s.mem.write (s.gpr .x1) 1 (s.mem (s.gpr .x1) ^^^ tbyte s.v X.toNat) ∧
      t.gpr .x1 = s.gpr .x1 + 1 ∧ t.gpr .x2 = s.gpr .x2 - 1 ∧
      (∀ r, r ≠ .x1 → r ≠ .x2 → r ≠ .x6 → r ≠ .x7 → t.gpr r = s.gpr r) ∧
      (∀ r, r ∉ outRegs → t.v r = s.v r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  obtain ⟨s₁, run₁, a₁, b₁, c₁, o₁⟩ := quarters_run (x := .v6) (a := .v1) (b := .v2) (c := .v3) hk X hx
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have x₁ : s₁.v .v6 = bc X := by rw [o₁.2 _ (by decide), hx]
  obtain ⟨s₂, run₂, v₂, o₂⟩ := lookup_run (d := .v7) (t := .v1) (x := .v6) (a := .v1) (b := .v2)
    (c := .v3) X x₁ a₁ b₁ c₁ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)
  have t₁ : tbyte s₁.v = tbyte s.v := by
    funext k; simp only [tbyte]
    rw [o₁.2 _ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨(show NotTable .v1 by decide).ne _, (show NotTable .v2 by decide).ne _,
        (show NotTable .v3 by decide).ne _⟩)]
  rw [t₁] at v₂
  have o : Only outRegs s s₂ := (o₁.mono (by decide)).trans (o₂.mono (by decide))
  rw [output, WP.block_append_iff, WP.block_append_iff]
  refine WP.of_runBlock ⟨s₁, run₁, WP.of_runBlock ⟨s₂, run₂, ?_⟩⟩
  have hd₂ : InRegions s₂.wr (s₂.gpr .x1) 1 := by rw [o.wr, o.gpr]; exact hd
  refine WP.mono (outScalar_ok v₂ hd₂) fun t ⟨m, x1, x2, g, v, rd, wr, sp⟩ => ?_
  refine ⟨by rw [m, o.mem, o.gpr], by rw [x1, o.gpr], by rw [x2, o.gpr],
    fun r a b c d => by rw [g r a b c d, o.gpr], fun r hr => by rw [v, o.2 r hr],
    by rw [rd, o.rd], by rw [wr, o.wr], by rw [sp, o.sp]⟩

end VG.Proof.Rc4.AArch64
