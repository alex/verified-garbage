import VerifiedGarbage.Proof.ChaCha20.X86.Stream.Init
import VerifiedGarbage.Proof.ChaCha20.X86.Xor

/-!
# Streaming ChaCha20 on x86 (32-bit): XORing bytes

Untrusted: everything here is checked by Lean. `xorBytes` XORs the `ecx`
bytes at `edx` into those at `esi`, one at a time, advancing both (the
loop of `vg_chacha20_xor`, `Xor.xorLoop`, which reads the keystream a word
at a time and uses its low byte).
-/

namespace VG.Proof.ChaCha20.X86.Stream

open VG VG.X86 VG.Impl.ChaCha20.X86.Stream
open VG.Impl.ChaCha20.X86 (at_)
open VG.Impl.ChaCha20.X86.Xor (xorBody xorLoop)
open VG.Proof.ChaCha20.X86.Xor (writeW8_apply low_byte xor_low ptr_add add_ofNat_one toNat_ofNat_lt32)

/-- What `xorBytes` needs: `c` bytes at `D` to write and at `K` to read (a
word at a time), not overlapping. -/
structure BPre (s : State) (D K : BitVec 32) (c : Nat) : Prop where
  esi : s.gpr .esi = D
  edx : s.gpr .edx = K
  ecx : s.gpr .ecx = BitVec.ofNat 32 c
  d_fit : D.toNat + c ≤ 2 ^ 32
  k_fit : K.toNat + c < 2 ^ 32
  wD : ∀ k < c, InRegions s.wr (D.setWidth 64 + BitVec.ofNat 64 k) 1
  rK : ∀ k < c, InRegions (s.rd ++ s.wr) (K.setWidth 64 + BitVec.ofNat 64 k) 4
  sep : ∀ j < c, ∀ k < c, D.setWidth 64 + BitVec.ofNat 64 j ≠ K.setWidth 64 + BitVec.ofNat 64 k

/-- What `xorBytes` leaves: the bytes XORed, and `esi`, `edx` past them;
only `eax`, `ecx`, `edx` and `esi` are written. -/
structure BPost (s : State) (D K : BitVec 32) (c : Nat) (s' : State) : Prop where
  esi : s'.gpr .esi = D + BitVec.ofNat 32 c
  keep : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → r ≠ .esi → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  data : ∀ k < c, s'.mem (D.setWidth 64 + BitVec.ofNat 64 k) =
    s.mem (D.setWidth 64 + BitVec.ofNat 64 k) ^^^ s.mem (K.setWidth 64 + BitVec.ofNat 64 k)
  frame : Frame [⟨D.setWidth 64, c⟩] s.mem s'.mem

/-- Before byte `i`. -/
structure LInv (s : State) (D K : BitVec 32) (c i : Nat) (s' : State) : Prop where
  esi : s'.gpr .esi = D + BitVec.ofNat 32 i
  edx : s'.gpr .edx = K + BitVec.ofNat 32 i
  ecx : s'.gpr .ecx = BitVec.ofNat 32 (c - i)
  keep : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → r ≠ .esi → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  data : ∀ k < c, s'.mem (D.setWidth 64 + BitVec.ofNat 64 k) =
    if k < i then s.mem (D.setWidth 64 + BitVec.ofNat 64 k) ^^^ s.mem (K.setWidth 64 + BitVec.ofNat 64 k)
    else s.mem (D.setWidth 64 + BitVec.ofNat 64 k)
  frame : Frame [⟨D.setWidth 64, c⟩] s.mem s'.mem

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

theorem ofNat32_beq_zero {x : Nat} (hx : x < 2 ^ 32) : (BitVec.ofNat 32 x == 0) = decide (x = 0) := by
  by_cases h : x = 0
  · simp [h]
  · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro h'
    have := congrArg BitVec.toNat h'
    rw [toNat_ofNat_lt32 hx] at this
    exact h this

set_option simprocs false in
theorem byte_step {s : State} {D K : BitVec 32} {c i : Nat} (hp : BPre s D K c) (hi : i < c) {s₁ : State}
    (h : LInv s D K c i s₁) :
    WP isa (.block xorBody) s₁ fun s' => LInv s D K c (i + 1) s' ∧ s'.zf = some (decide (c - (i + 1) = 0)) := by
  have hc := hp.d_fit
  have hk := hp.k_fit
  have ea₁ : (D + BitVec.ofNat 32 i + BitVec.ofNat 32 0).setWidth 64 = D.setWidth 64 + BitVec.ofNat 64 i :=
    ptr_add _ (by omega)
  have ea₂ : (K + BitVec.ofNat 32 i + BitVec.ofNat 32 0).setWidth 64 = K.setWidth 64 + BitVec.ofNat 64 i :=
    ptr_add _ (by omega)
  have cd : (⟨D.setWidth 64, c⟩ : Region).Contains (D.setWidth 64 + BitVec.ofNat 64 i) 1 :=
    Offset.contains_base _ (by omega) (by omega)
  have i₁ : InRegions (s₁.rd ++ s₁.wr) (D.setWidth 64 + BitVec.ofNat 64 i) 1 := by
    obtain ⟨r, hr, hc⟩ := hp.wD i hi; exact ⟨r, by rw [h.rd, h.wr]; exact List.mem_append_right _ hr, hc⟩
  have i₂ : InRegions (s₁.rd ++ s₁.wr) (K.setWidth 64 + BitVec.ofNat 64 i) 4 := by
    rw [h.rd, h.wr]; exact hp.rK i hi
  have o₁ : InRegions s₁.wr (D.setWidth 64 + BitVec.ofNat 64 i) 1 := by rw [h.wr]; exact hp.wD i hi
  apply WP.of_runBlock
  simp (config := {decide := true}) only [xorBody, at_, runBlock_cons, runStep_some,
    runBlock_nil, exec, State.ea, readSrc, execAlu, arithFlags, State.load8, State.load32,
    State.store8, State.setReg, State.setFlags, Reg8.reg, h.esi, h.edx, ea₁, ea₂, i₁, i₂, o₁,
    ite_true, ite_false, Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  have hk' : s₁.mem (K.setWidth 64 + BitVec.ofNat 64 i) = s.mem (K.setWidth 64 + BitVec.ofNat 64 i) :=
    h.frame _ fun r hr hcont => by
      simp only [List.mem_singleton] at hr; subst hr
      exact not_contains hp.sep hi hcont
  have hd : s₁.mem (D.setWidth 64 + BitVec.ofNat 64 i) = s.mem (D.setWidth 64 + BitVec.ofNat 64 i) := by
    rw [h.data i hi]; simp
  rw [xor_low, low_byte, hd, hk']
  have hfd : Frame [⟨D.setWidth 64, c⟩] s₁.mem (s₁.mem.writeW (D.setWidth 64 + BitVec.ofNat 64 i)
      (s.mem (D.setWidth 64 + BitVec.ofNat 64 i) ^^^ s.mem (K.setWidth 64 + BitVec.ofNat 64 i))) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ cd
  have hsub : BitVec.ofNat 32 (c - i) - 1 = BitVec.ofNat 32 (c - (i + 1)) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, toNat_ofNat_lt32 (by omega)]; simp; omega),
      toNat_ofNat_lt32 (by omega), toNat_ofNat_lt32 (by omega)]
    simp; omega
  refine ⟨⟨?_, ?_, ?_, fun r h₁ h₂ h₃ h₄ => ?_, h.rd, h.wr, fun k hk' => ?_, h.frame.trans hfd⟩, ?_⟩
  · simp (config := {decide := true}) only [ite_true, ite_false]
    exact add_ofNat_one _ _
  · simp (config := {decide := true}) only [ite_true, ite_false]
    exact add_ofNat_one _ _
  · simp (config := {decide := true}) only [ite_true, ite_false, h.ecx]
    exact hsub
  · simp only [h₁, h₂, h₃, h₄, ite_false]; exact h.keep r h₁ h₂ h₃ h₄
  · dsimp only; rw [writeW8_apply]
    by_cases he : k = i
    · subst he; simp
    · have hne := D_ne (D := D.setWidth 64) (by omega) hk' hi he
      simp only [hne, ite_false]
      rw [h.data k hk']
      by_cases h₁ : k < i
      · simp [h₁, show k < i + 1 by omega]
      · simp [h₁, show ¬ k < i + 1 by omega]
  · simp only [h.ecx, hsub, ofNat32_beq_zero (show c - (i + 1) < 2 ^ 32 by omega)]

theorem LInv.zero {s : State} {D K : BitVec 32} {c : Nat} (hp : BPre s D K c) : LInv s D K c 0 s :=
  ⟨by rw [hp.esi]; simp, by rw [hp.edx]; simp, by rw [hp.ecx, Nat.sub_zero], fun _ _ _ _ _ => rfl, rfl, rfl,
    fun k _ => by simp, Frame.refl _ _⟩

theorem LInv.post {s : State} {D K : BitVec 32} {c : Nat} {s' : State} (h : LInv s D K c c s') :
    BPost s D K c s' :=
  ⟨h.esi, h.keep, h.rd, h.wr, fun k hk => by rw [h.data k hk, ite_pos hk], h.frame⟩

theorem loop_ok {s : State} {D K : BitVec 32} {c : Nat} (hp : BPre s D K c) (hc0 : c ≠ 0) :
    WP isa xorLoop s (BPost s D K c) := by
  have hc := hp.d_fit
  let Inv : Nat → State → Prop := fun n s' => ∃ i, n = c - i ∧ i < c ∧ LInv s D K c i s'
  have hstep : ∀ n s', Inv n s' → WP isa (.block xorBody) s' (fun s'' =>
      (isa.eval .ne s'' = some false ∧ BPost s D K c s'') ∨
      (isa.eval .ne s'' = some true ∧ ∃ n' < n, Inv n' s'')) := by
    rintro n s' ⟨i, rfl, hi, hI⟩
    refine WP.mono (byte_step hp hi hI) fun s'' ⟨h', hz⟩ => ?_
    have he : isa.eval .ne s'' = some (!decide (c - (i + 1) = 0)) := by
      show eval .ne s'' = _
      simp only [eval, hz, Option.map_some]
    by_cases hl : i + 1 = c
    · exact .inl ⟨by rw [he]; simp; omega, LInv.post (hl ▸ h')⟩
    · exact .inr ⟨by rw [he]; simp; omega, c - (i + 1), by omega, i + 1, rfl, by omega, h'⟩
  exact WP.loop (M := isa) Inv hstep c s ⟨0, by simp, by omega, LInv.zero hp⟩

set_option simprocs false in
theorem test_ecx_ok {s : State} {c : Nat} (h : s.gpr .ecx = BitVec.ofNat 32 c) (hc : c < 2 ^ 32) :
    WP isa (.block [.alu .test .ecx (.reg .ecx)]) s fun s' => s'.gpr = s.gpr ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.zf = some (decide (c = 0)) := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, arithFlags, State.setFlags,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, trivial, trivial, ?_⟩
  rw [BitVec.and_self, h, ofNat32_beq_zero hc]

theorem xorBytes_eq : xorBytes = .seq (.block [.alu .test .ecx (.reg .ecx)]) (.ite .e (.block []) xorLoop) := rfl

theorem xorBytes_ok {s : State} {D K : BitVec 32} {c : Nat} (hp : BPre s D K c) :
    WP isa xorBytes s (BPost s D K c) := by
  have hc := hp.d_fit
  rw [xorBytes_eq]
  refine WP.seq (WP.mono (test_ecx_ok hp.ecx (by have := hp.k_fit; omega)) fun s₁ ⟨g₁, m₁, r₁, w₁, z₁⟩ => ?_)
  have hp₁ : BPre s₁ D K c := ⟨by rw [g₁, hp.esi], by rw [g₁, hp.edx], by rw [g₁, hp.ecx], hp.d_fit, hp.k_fit,
    fun k hk => by rw [w₁]; exact hp.wD k hk, fun k hk => by rw [r₁, w₁]; exact hp.rK k hk,
    hp.sep⟩
  have conv : ∀ s', BPost s₁ D K c s' → BPost s D K c s' := fun s' h =>
    ⟨h.esi, fun r a b d e => by rw [h.keep r a b d e, g₁], by rw [h.rd, r₁], by rw [h.wr, w₁],
      fun k hk => by rw [h.data k hk, m₁], m₁ ▸ h.frame⟩
  refine WP.ite (decide (c = 0)) (by show eval .e s₁ = _; simp only [eval, z₁])
    (fun h0 => WP.block_nil (M := isa) (conv _ ?_)) (fun h0 => WP.mono (loop_ok hp₁ (by simpa using h0)) conv)
  simp only [decide_eq_true_eq] at h0; subst h0; exact (LInv.zero hp₁).post

end VG.Proof.ChaCha20.X86.Stream
