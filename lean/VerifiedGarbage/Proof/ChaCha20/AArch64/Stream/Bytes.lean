import VerifiedGarbage.Proof.ChaCha20.AArch64.Stream.Init

/-!
# Streaming ChaCha20 on AArch64: XORing bytes

Untrusted: everything here is checked by Lean. `xorBytes` XORs the `x2`
bytes at `x1` into those at `x22`, one at a time, advancing both and
counting them off `x2` and `x23`.
-/

namespace VG.Proof.ChaCha20.AArch64.Stream

open VG VG.AArch64 VG.Impl.ChaCha20.AArch64.Stream
open VG.Proof.ChaCha20.AArch64.Xor (wp_ldrb wp_strb wp_eor32 wp_addImm wp_subImm xor_setWidth writeW8_apply
  eval_nonzero_ofNat sub_ofNat add_ofNat)
open VG.Proof.ChaCha20.AArch64 (toNat_ofNat_lt)

/-- What `xorBytes` needs: `c` bytes at `D` to write and at `K` to read, not
overlapping. -/
structure BPre (s : State) (D K : Addr) (c : Nat) : Prop where
  x22 : s.gpr .x22 = D
  x1 : s.gpr .x1 = K
  x2 : s.gpr .x2 = BitVec.ofNat 64 c
  c_lt : c ≤ 2 ^ 32
  wD : ∀ k < c, InRegions s.wr (D + BitVec.ofNat 64 k) 1
  rK : ∀ k < c, InRegions (s.rd ++ s.wr) (K + BitVec.ofNat 64 k) 1
  sep : ∀ j < c, ∀ k < c, D + BitVec.ofNat 64 j ≠ K + BitVec.ofNat 64 k

/-- What `xorBytes` leaves: the bytes XORed, `x22` past them and `x23` less
their number; only `x1`, `x2`, `x9`, `x10`, `x22` and `x23` are written. -/
structure BPost (s : State) (D K : Addr) (c : Nat) (s' : State) : Prop where
  x22 : s'.gpr .x22 = D + BitVec.ofNat 64 c
  x23 : s'.gpr .x23 = s.gpr .x23 - BitVec.ofNat 64 c
  keep : ∀ r, r ≠ .x1 → r ≠ .x2 → r ≠ .x9 → r ≠ .x10 → r ≠ .x22 → r ≠ .x23 → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  data : ∀ k < c, s'.mem (D + BitVec.ofNat 64 k) = s.mem (D + BitVec.ofNat 64 k) ^^^ s.mem (K + BitVec.ofNat 64 k)
  frame : Frame [⟨D, c⟩] s.mem s'.mem

/-- Before byte `i`. -/
structure LInv (s : State) (D K : Addr) (c i : Nat) (s' : State) : Prop where
  x22 : s'.gpr .x22 = D + BitVec.ofNat 64 i
  x1 : s'.gpr .x1 = K + BitVec.ofNat 64 i
  x2 : s'.gpr .x2 = BitVec.ofNat 64 (c - i)
  x23 : s'.gpr .x23 = s.gpr .x23 - BitVec.ofNat 64 i
  keep : ∀ r, r ≠ .x1 → r ≠ .x2 → r ≠ .x9 → r ≠ .x10 → r ≠ .x22 → r ≠ .x23 → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  data : ∀ k < c, s'.mem (D + BitVec.ofNat 64 k) =
    if k < i then s.mem (D + BitVec.ofNat 64 k) ^^^ s.mem (K + BitVec.ofNat 64 k) else s.mem (D + BitVec.ofNat 64 k)
  frame : Frame [⟨D, c⟩] s.mem s'.mem

theorem D_ne {D : Addr} {c j k : Nat} (hc : c ≤ 2 ^ 32) (hj : j < c) (hk : k < c) (h : j ≠ k) :
    D + BitVec.ofNat 64 j ≠ D + BitVec.ofNat 64 k := by
  intro he
  have e : BitVec.ofNat 64 j = BitVec.ofNat 64 k := by
    have e := congrArg (· - D) he; simpa using e
  have := congrArg BitVec.toNat e
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
  exact h this

/-- A byte read is outside the bytes written. -/
theorem not_contains {D K : Addr} {c i : Nat}
    (hs : ∀ j < c, ∀ k < c, D + BitVec.ofNat 64 j ≠ K + BitVec.ofNat 64 k) (hi : i < c)
    (h : (⟨D, c⟩ : Region).Contains (K + BitVec.ofNat 64 i) 1) : False := by
  simp only [Region.Contains] at h
  refine hs (K + BitVec.ofNat 64 i - D).toNat (by omega) i hi ?_
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]

/-- The loop's body. -/
def body : List Instr :=
  [.ldrb .x9 .x22 0, .ldrb .x10 .x1 0, .logic .eor .w .x9 .x9 .x10, .strb .x9 .x22 0,
    .addImm .x .x22 .x22 1, .addImm .x .x1 .x1 1, .subImm .x .x2 .x2 1, .subImm .x .x23 .x23 1]

theorem byte_step {s : State} {D K : Addr} {c i : Nat} (hp : BPre s D K c) (hi : i < c) {s₁ : State}
    (h : LInv s D K c i s₁) : WP isa (.block body) s₁ (LInv s D K c (i + 1)) := by
  have hc := hp.c_lt
  have i₁ : InRegions (s₁.rd ++ s₁.wr) (D + BitVec.ofNat 64 i) 1 := by
    obtain ⟨r, hr, hc⟩ := hp.wD i hi; exact ⟨r, by rw [h.rd, h.wr]; exact List.mem_append_right _ hr, hc⟩
  have i₂ : InRegions (s₁.rd ++ s₁.wr) (K + BitVec.ofNat 64 i) 1 := by rw [h.rd, h.wr]; exact hp.rK i hi
  have o₁ : InRegions s₁.wr (D + BitVec.ofNat 64 i) 1 := by rw [h.wr]; exact hp.wD i hi
  have cd : (⟨D, c⟩ : Region).Contains (D + BitVec.ofNat 64 i) 1 := Offset.contains_base D (by omega) (by omega)
  unfold body
  refine wp_ldrb (a := D + BitVec.ofNat 64 i) (by decide) (by rw [h.x22]; exact BitVec.add_zero _) i₁
    fun s₂ u₂ => ?_
  refine wp_ldrb (a := K + BitVec.ofNat 64 i) (by decide)
    (by rw [u₂.other _ (by decide), h.x1]; exact BitVec.add_zero _) (by rw [u₂.rd, u₂.wr]; exact i₂)
    fun s₃ u₃ => ?_
  refine wp_eor32 fun s₄ u₄ => ?_
  refine wp_strb (a := D + BitVec.ofNat 64 i) (by decide)
    (by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), h.x22]
        exact BitVec.add_zero _)
    (by rw [u₄.wr, u₃.wr, u₂.wr]; exact o₁) fun s₅ g₅ => ?_
  refine wp_addImm (by decide) fun s₆ u₆ => wp_addImm (by decide) fun s₇ u₇ =>
    wp_subImm (by decide) fun s₈ u₈ => wp_subImm (by decide) fun s₉ u₉ => WP.block_nil ?_
  have hk : s₁.mem (K + BitVec.ofNat 64 i) = s.mem (K + BitVec.ofNat 64 i) :=
    h.frame _ fun r hr hcont => by
      simp only [List.mem_singleton] at hr; subst hr
      exact not_contains hp.sep hi hcont
  have hv : (s₄.gpr .x9).setWidth 8 = s.mem (D + BitVec.ofNat 64 i) ^^^ s.mem (K + BitVec.ofNat 64 i) := by
    rw [u₄.gpr, u₃.other _ (by decide), u₂.gpr, u₃.gpr, u₂.mem, xor_setWidth, h.data _ hi, hk]
    simp
  have hm : s₉.mem = s₁.mem.writeW (D + BitVec.ofNat 64 i)
      (s.mem (D + BitVec.ofNat 64 i) ^^^ s.mem (K + BitVec.ofNat 64 i)) := by
    rw [u₉.mem, u₈.mem, u₇.mem, u₆.mem, g₅.mem, hv, u₄.mem, u₃.mem, u₂.mem]
  have g : ∀ r, r ≠ .x1 → r ≠ .x2 → r ≠ .x9 → r ≠ .x10 → r ≠ .x22 → r ≠ .x23 → s₉.gpr r = s₁.gpr r :=
    fun r h₁ h₂ h₃ h₄ h₅ h₆ => by
      rw [u₉.other r h₆, u₈.other r h₂, u₇.other r h₁, u₆.other r h₅, g₅.gpr, u₄.other r h₃, u₃.other r h₄,
        u₂.other r h₃]
  have hfd : Frame [⟨D, c⟩] s₁.mem s₉.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ cd
  refine ⟨?_, ?_, ?_, ?_, fun r h₁ h₂ h₃ h₄ h₅ h₆ => by rw [g r h₁ h₂ h₃ h₄ h₅ h₆]; exact h.keep r h₁ h₂ h₃ h₄ h₅ h₆,
    by rw [u₉.rd, u₈.rd, u₇.rd, u₆.rd, g₅.rd, u₄.rd, u₃.rd, u₂.rd, h.rd],
    by rw [u₉.wr, u₈.wr, u₇.wr, u₆.wr, g₅.wr, u₄.wr, u₃.wr, u₂.wr, h.wr], fun k hk' => ?_, h.frame.trans hfd⟩
  · rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, g₅.gpr,
      u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), h.x22, add_ofNat]
  · rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr, u₆.other _ (by decide), g₅.gpr,
      u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), h.x1, add_ofNat]
  · rw [u₉.other _ (by decide), u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), g₅.gpr,
      u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), h.x2, sub_ofNat (by omega),
      Nat.sub_sub]
  · rw [u₉.gpr, u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), g₅.gpr,
      u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), h.x23, BitVec.sub_sub,
      BitVec.ofNat_add]
  · rw [hm, writeW8_apply]
    by_cases he : k = i
    · subst he; simp
    · simp only [D_ne hc hk' hi he, ite_false]
      rw [h.data k hk']
      by_cases h₁ : k < i
      · simp [h₁, show k < i + 1 by omega]
      · simp [h₁, show ¬ k < i + 1 by omega]


theorem xorBytes_eq : xorBytes = .ite (.zero .x .x2) (.block []) (.loop (.block body) (.nonzero .x .x2)) := rfl

theorem LInv.zero {s : State} {D K : Addr} {c : Nat} (hp : BPre s D K c) : LInv s D K c 0 s :=
  ⟨by rw [hp.x22]; simp, by rw [hp.x1]; simp, by rw [hp.x2, Nat.sub_zero], by simp,
    fun _ _ _ _ _ _ _ => rfl, rfl, rfl, fun k _ => by simp, Frame.refl _ _⟩

theorem LInv.post {s : State} {D K : Addr} {c : Nat} {s' : State} (h : LInv s D K c c s') : BPost s D K c s' :=
  ⟨h.x22, h.x23, h.keep, h.rd, h.wr, fun k hk => by rw [h.data k hk, ite_pos hk], h.frame⟩

theorem xorBytes_ok {s : State} {D K : Addr} {c : Nat} (hp : BPre s D K c) :
    WP isa xorBytes s (BPost s D K c) := by
  have hc := hp.c_lt
  rw [xorBytes_eq]
  refine WP.ite (decide (c = 0)) (by
      have e : isa.eval (.zero .x .x2) s = some (s.gpr .x2 == 0) := Proof.ChaCha20.AArch64.Xor.eval_zero s .x2
      rw [e, hp.x2, Proof.ChaCha20.AArch64.Xor.ofNat_beq_zero (by omega)])
    (fun h0 => WP.block_nil (M := isa) ?_) (fun h0 => ?_)
  · simp only [decide_eq_true_eq] at h0; subst h0; exact (LInv.zero hp).post
  · simp only [decide_eq_false_iff_not] at h0
    let Inv : Nat → State → Prop := fun n s' => ∃ i, n = c - i ∧ i < c ∧ LInv s D K c i s'
    have hstep : ∀ n s', Inv n s' → WP isa (.block body) s' (fun s'' =>
        (isa.eval (.nonzero .x .x2) s'' = some false ∧ BPost s D K c s'') ∨
        (isa.eval (.nonzero .x .x2) s'' = some true ∧ ∃ n' < n, Inv n' s'')) := by
      rintro n s' ⟨i, rfl, hi, hI⟩
      refine WP.mono (byte_step hp hi hI) fun s'' h' => ?_
      have hz := eval_nonzero_ofNat s'' .x2 (by omega) h'.x2
      by_cases hl : i + 1 = c
      · exact .inl ⟨by rw [hz]; simp; omega, LInv.post (hl ▸ h')⟩
      · exact .inr ⟨by rw [hz]; simp; omega, c - (i + 1), by omega, i + 1, rfl, by omega, h'⟩
    exact WP.loop (M := isa) Inv hstep c s ⟨0, by simp, by omega, LInv.zero hp⟩

end VG.Proof.ChaCha20.AArch64.Stream
