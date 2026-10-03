import VerifiedGarbage.Proof.ChaCha20.Arm.Stream.Init
import VerifiedGarbage.Proof.ChaCha20.Arm.Xor

/-!
# Streaming ChaCha20 on ARMv7: XORing bytes

Untrusted: everything here is checked by Lean. `xorBytes` XORs the `r2`
bytes at `r3` into those at `r5`, one at a time, advancing both (the loop of
`vg_chacha20_xor`, `Xor.xorLoop`).
-/

namespace VG.Proof.ChaCha20.Arm.Stream

open VG VG.Arm VG.Impl.ChaCha20.Arm.Stream
open VG.Impl.ChaCha20.Arm.Xor (xorLoop)
open VG.Proof.ChaCha20.Arm.Xor (xorBody xorLoop_eq wp_eor imm0 imm1 ea0 xor_setWidth writeW8_apply add_one'
  sub_one' sub_zero' eval_ne_ofNat)
open VG.Proof.MdStream.Arm (Upd Mupd Fupd op2_imm op2_reg wp_add wp_subs wp_cmp wp_ldrb wp_strb eval_eq
  ofNat_beq_zero)

/-- What `xorBytes` needs: `c` bytes at `D` to write and at `K` to read, not
overlapping. -/
structure BPre (s : State) (D K : BitVec 32) (c : Nat) : Prop where
  r5 : s.gpr .r5 = D
  r3 : s.gpr .r3 = K
  r2 : s.gpr .r2 = BitVec.ofNat 32 c
  d_fit : D.toNat + c ≤ 2 ^ 32
  k_fit : K.toNat + c < 2 ^ 32
  wD : ∀ k < c, InRegions s.wr (State.addr D + BitVec.ofNat 64 k) 1
  rK : ∀ k < c, InRegions (s.rd ++ s.wr) (State.addr K + BitVec.ofNat 64 k) 1
  sep : ∀ j < c, ∀ k < c, State.addr D + BitVec.ofNat 64 j ≠ State.addr K + BitVec.ofNat 64 k

/-- What `xorBytes` leaves: the bytes XORed, and `r5` past them; only `r0`,
`r2`, `r3`, `r5` and `r12` are written. -/
structure BPost (s : State) (D K : BitVec 32) (c : Nat) (s' : State) : Prop where
  r5 : s'.gpr .r5 = D + BitVec.ofNat 32 c
  keep : ∀ r, r ≠ .r0 → r ≠ .r2 → r ≠ .r3 → r ≠ .r5 → r ≠ .r12 → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  data : ∀ k < c, s'.mem (State.addr D + BitVec.ofNat 64 k) =
    s.mem (State.addr D + BitVec.ofNat 64 k) ^^^ s.mem (State.addr K + BitVec.ofNat 64 k)
  frame : Frame [⟨State.addr D, c⟩] s.mem s'.mem

/-- Before byte `i`. -/
structure LInv (s : State) (D K : BitVec 32) (c i : Nat) (s' : State) : Prop where
  r5 : s'.gpr .r5 = D + BitVec.ofNat 32 i
  r3 : s'.gpr .r3 = K + BitVec.ofNat 32 i
  r2 : s'.gpr .r2 = BitVec.ofNat 32 (c - i)
  keep : ∀ r, r ≠ .r0 → r ≠ .r2 → r ≠ .r3 → r ≠ .r5 → r ≠ .r12 → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  data : ∀ k < c, s'.mem (State.addr D + BitVec.ofNat 64 k) =
    if k < i then s.mem (State.addr D + BitVec.ofNat 64 k) ^^^ s.mem (State.addr K + BitVec.ofNat 64 k)
    else s.mem (State.addr D + BitVec.ofNat 64 k)
  frame : Frame [⟨State.addr D, c⟩] s.mem s'.mem

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

theorem byte_step {s : State} {D K : BitVec 32} {c i : Nat} (hp : BPre s D K c) (hi : i < c) {s₁ : State}
    (h : LInv s D K c i s₁) :
    WP isa (.block xorBody) s₁ fun s' => LInv s D K c (i + 1) s' ∧ s'.z = (s'.gpr .r2 - 0 == 0) := by
  have hc := hp.d_fit
  have hk := hp.k_fit
  have cd : (⟨State.addr D, c⟩ : Region).Contains (State.addr D + BitVec.ofNat 64 i) 1 :=
    Offset.contains_base _ (by omega) (by omega)
  have i₁ : InRegions (s₁.rd ++ s₁.wr) (State.addr D + BitVec.ofNat 64 i) 1 := by
    obtain ⟨r, hr, hc⟩ := hp.wD i hi; exact ⟨r, by rw [h.rd, h.wr]; exact List.mem_append_right _ hr, hc⟩
  have i₂ : InRegions (s₁.rd ++ s₁.wr) (State.addr K + BitVec.ofNat 64 i) 1 := by
    rw [h.rd, h.wr]; exact hp.rK i hi
  have o₁ : InRegions s₁.wr (State.addr D + BitVec.ofNat 64 i) 1 := by rw [h.wr]; exact hp.wD i hi
  have ed : ∀ x : State, x.gpr .r5 = s₁.gpr .r5 →
      State.addr (x.gpr .r5 + BitVec.ofNat 32 0) = State.addr D + BitVec.ofNat 64 i :=
    fun x hx => by rw [hx, h.r5]; exact ea0 (by omega)
  unfold xorBody
  refine wp_ldrb (by decide) (ed s₁ rfl) i₁ fun s₂ u₂ => ?_
  refine wp_ldrb (a := State.addr K + BitVec.ofNat 64 i) (by decide)
    (by rw [u₂.other _ (by decide), h.r3]; exact ea0 (by omega))
    (by rw [u₂.rd, u₂.wr]; exact i₂) fun s₃ u₃ => ?_
  refine wp_eor (op2_reg _ _) fun s₄ u₄ => ?_
  refine wp_strb (by decide) (ed s₄ (by rw [u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide)]))
    (by rw [u₄.wr, u₃.wr, u₂.wr]; exact o₁) fun s₅ g₅ => ?_
  refine wp_add (op2_imm imm1) fun s₆ u₆ => wp_add (op2_imm imm1) fun s₇ u₇ =>
    wp_subs (op2_imm imm1) fun s₈ u₈ hz => WP.block_nil ?_
  have hk' : s₁.mem (State.addr K + BitVec.ofNat 64 i) = s.mem (State.addr K + BitVec.ofNat 64 i) :=
    h.frame _ fun r hr hcont => by
      simp only [List.mem_singleton] at hr; subst hr
      exact not_contains hp.sep hi hcont
  have hv : (s₄.gpr .r0).setWidth 8 =
      s.mem (State.addr D + BitVec.ofNat 64 i) ^^^ s.mem (State.addr K + BitVec.ofNat 64 i) := by
    rw [u₄.gpr, u₃.other _ (by decide), u₂.gpr, u₃.gpr, u₂.mem, xor_setWidth, h.data _ hi, hk']
    simp
  have hm : s₈.mem = s₁.mem.writeW (State.addr D + BitVec.ofNat 64 i)
      (s.mem (State.addr D + BitVec.ofNat 64 i) ^^^ s.mem (State.addr K + BitVec.ofNat 64 i)) := by
    rw [u₈.mem, u₇.mem, u₆.mem, g₅.mem, hv, u₄.mem, u₃.mem, u₂.mem]
  have hfd : Frame [⟨State.addr D, c⟩] s₁.mem s₈.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ cd
  have g : ∀ r, r ≠ .r0 → r ≠ .r2 → r ≠ .r3 → r ≠ .r5 → r ≠ .r12 → s₈.gpr r = s₁.gpr r :=
    fun r h₁ h₂ h₃ h₄ h₅ => by
      rw [u₈.other r h₂, u₇.other r h₃, u₆.other r h₄, g₅.gpr, u₄.other r h₁, u₃.other r h₅,
        u₂.other r h₁]
  have h7 : s₇.gpr .r2 = BitVec.ofNat 32 (c - i) := by
    rw [u₇.other _ (by decide), u₆.other _ (by decide), g₅.gpr, u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), h.r2]
  have hr2 : s₈.gpr .r2 = BitVec.ofNat 32 (c - (i + 1)) := by
    rw [u₈.gpr, h7, sub_one' (by omega), Nat.sub_sub]
  refine ⟨⟨?_, ?_, hr2, fun r h₁ h₂ h₃ h₄ h₅ => by rw [g r h₁ h₂ h₃ h₄ h₅]; exact h.keep r h₁ h₂ h₃ h₄ h₅,
    by rw [u₈.rd, u₇.rd, u₆.rd, g₅.rd, u₄.rd, u₃.rd, u₂.rd, h.rd],
    by rw [u₈.wr, u₇.wr, u₆.wr, g₅.wr, u₄.wr, u₃.wr, u₂.wr, h.wr],
    by rw [u₈.sp, u₇.sp, u₆.sp, g₅.sp, u₄.sp, u₃.sp, u₂.sp, h.sp], fun k hk' => ?_, h.frame.trans hfd⟩, ?_⟩
  · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, g₅.gpr, u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), h.r5, add_one']
  · rw [u₈.other _ (by decide), u₇.gpr, u₆.other _ (by decide), g₅.gpr, u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), h.r3, add_one']
  · rw [hm, writeW8_apply]
    by_cases he : k = i
    · subst he; simp
    · simp only [D_ne (D := State.addr D) (by omega) hk' hi he, ite_false]
      rw [h.data k hk']
      by_cases h₁ : k < i
      · simp [h₁, show k < i + 1 by omega]
      · simp [h₁, show ¬ k < i + 1 by omega]
  · rw [hz, hr2, h7, sub_one' (by omega), sub_zero', Nat.sub_sub]

theorem LInv.zero {s : State} {D K : BitVec 32} {c : Nat} (hp : BPre s D K c) : LInv s D K c 0 s :=
  ⟨by rw [hp.r5]; simp, by rw [hp.r3]; simp, by rw [hp.r2, Nat.sub_zero], fun _ _ _ _ _ _ => rfl, rfl, rfl,
    rfl, fun k _ => by simp, Frame.refl _ _⟩

theorem LInv.post {s : State} {D K : BitVec 32} {c : Nat} {s' : State} (h : LInv s D K c c s') :
    BPost s D K c s' :=
  ⟨h.r5, h.keep, h.rd, h.wr, h.sp, fun k hk => by rw [h.data k hk, ite_pos hk], h.frame⟩

theorem loop_ok {s : State} {D K : BitVec 32} {c : Nat} (hp : BPre s D K c) (hc0 : c ≠ 0) :
    WP isa xorLoop s (BPost s D K c) := by
  have hc := hp.d_fit
  rw [xorLoop_eq]
  let Inv : Nat → State → Prop := fun n s' => ∃ i, n = c - i ∧ i < c ∧ LInv s D K c i s'
  have hstep : ∀ n s', Inv n s' → WP isa (.block xorBody) s' (fun s'' =>
      (isa.eval .ne s'' = some false ∧ BPost s D K c s'') ∨
      (isa.eval .ne s'' = some true ∧ ∃ n' < n, Inv n' s'')) := by
    rintro n s' ⟨i, rfl, hi, hI⟩
    refine WP.mono (byte_step hp hi hI) fun s'' ⟨h', hz'⟩ => ?_
    have hz := eval_ne_ofNat s'' (show c - (i + 1) < 2 ^ 32 by omega) hz' h'.r2
    by_cases hl : i + 1 = c
    · exact .inl ⟨by rw [hz]; simp; omega, LInv.post (hl ▸ h')⟩
    · exact .inr ⟨by rw [hz]; simp; omega, c - (i + 1), by omega, i + 1, rfl, by omega, h'⟩
  exact WP.loop (M := isa) Inv hstep c s ⟨0, by simp, by omega, LInv.zero hp⟩

theorem xorBytes_eq : xorBytes = .seq (.block [.cmp .r2 (.imm 0)]) (.ite .eq (.block []) xorLoop) := rfl

theorem xorBytes_ok {s : State} {D K : BitVec 32} {c : Nat} (hp : BPre s D K c) :
    WP isa xorBytes s (BPost s D K c) := by
  have hc := hp.k_fit
  rw [xorBytes_eq]
  refine WP.seq (wp_cmp (n := .r2) (op2_imm imm0) fun s₁ f₁ hz => WP.block_nil ?_)
  have hp₁ : BPre s₁ D K c := ⟨by rw [f₁.gpr, hp.r5], by rw [f₁.gpr, hp.r3], by rw [f₁.gpr, hp.r2], hp.d_fit,
    hp.k_fit, fun k hk => by rw [f₁.wr]; exact hp.wD k hk, fun k hk => by rw [f₁.rd, f₁.wr]; exact hp.rK k hk,
    hp.sep⟩
  have conv : ∀ s', BPost s₁ D K c s' → BPost s D K c s' := fun s' h =>
    ⟨h.r5, fun r a b d e f => by rw [h.keep r a b d e f, f₁.gpr], by rw [h.rd, f₁.rd], by rw [h.wr, f₁.wr],
      by rw [h.sp, f₁.sp], fun k hk => by rw [h.data k hk, f₁.mem], f₁.mem ▸ h.frame⟩
  refine WP.ite (decide (c = 0)) (by
      have e : isa.eval .eq s₁ = some s₁.z := eval_eq s₁
      rw [e, hz, hp.r2, sub_zero', ofNat_beq_zero (by omega)])
    (fun h0 => WP.block_nil (M := isa) (conv _ ?_)) (fun h0 => WP.mono (loop_ok hp₁ (by simpa using h0)) conv)
  simp only [decide_eq_true_eq] at h0; subst h0; exact (LInv.zero hp₁).post

end VG.Proof.ChaCha20.Arm.Stream
