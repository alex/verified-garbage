import VerifiedGarbage.Proof.ChaCha20.X86_64.Stream.Init
import VerifiedGarbage.Proof.ChaCha20.X86_64.Xor

/-!
# Streaming ChaCha20 on x86-64: XORing bytes

Untrusted: everything here is checked by Lean. `xorBytes` XORs the `rdx`
bytes at `rsi` into those at `rbp`, one at a time.
-/

namespace VG.Proof.ChaCha20.X86_64.Stream

open VG VG.X86_64 VG.Impl.ChaCha20.X86_64.Stream
open VG.Impl.ChaCha20.X86_64.Xor (xorLoop dataByte ksByte)
open VG.Proof.ChaCha20.X86_64 (toNat_ofNat_lt)
open VG.Proof.ChaCha20.X86_64.Xor (xorBody xorLoop_eq writeW8_apply xor_setWidth se1)

/-- What `xorBytes` needs: `c` bytes at `D` to write and at `K` to read, not
overlapping. -/
structure BPre (s : State) (D K : Addr) (c : Nat) : Prop where
  rbp : s.gpr .rbp = D
  rsi : s.gpr .rsi = K
  rdx : s.gpr .rdx = BitVec.ofNat 64 c
  c_lt : c ≤ 2 ^ 32
  wD : ∀ k < c, InRegions s.wr (D + BitVec.ofNat 64 k) 1
  rK : ∀ k < c, InRegions (s.rd ++ s.wr) (K + BitVec.ofNat 64 k) 1
  sep : ∀ j < c, ∀ k < c, D + BitVec.ofNat 64 j ≠ K + BitVec.ofNat 64 k

/-- What `xorBytes` leaves: the bytes XORed, `rbp` past them and `r12`
less their number; only `rax`, `r8`, `rcx`, `rbp`, `r12` and the flags are
written. -/
structure BPost (s : State) (D K : Addr) (c : Nat) (s' : State) : Prop where
  rbp : s'.gpr .rbp = D + BitVec.ofNat 64 c
  r12 : s'.gpr .r12 = s.gpr .r12 - BitVec.ofNat 64 c
  keep : ∀ r, r ≠ .rax → r ≠ .r8 → r ≠ .rcx → r ≠ .rbp → r ≠ .r12 → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  data : ∀ k < c, s'.mem (D + BitVec.ofNat 64 k) = s.mem (D + BitVec.ofNat 64 k) ^^^ s.mem (K + BitVec.ofNat 64 k)
  frame : Frame [⟨D, c⟩] s.mem s'.mem

/-- Before byte `i`. -/
structure LInv (s : State) (D K : Addr) (c i : Nat) (s' : State) : Prop where
  rcx : s'.gpr .rcx = BitVec.ofNat 64 i
  keep : ∀ r, r ≠ .rax → r ≠ .r8 → r ≠ .rcx → s'.gpr r = s.gpr r
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
  rw [toNat_ofNat_lt (by omega), toNat_ofNat_lt (by omega)] at this
  exact h this

theorem contains_byte {D : Addr} {c k : Nat} (hk : k < c) (hc : c ≤ 2 ^ 32) :
    (⟨D, c⟩ : Region).Contains (D + BitVec.ofNat 64 k) 1 :=
  Offset.contains_base D (by omega) (by omega)

/-- A byte read is outside the bytes written. -/
theorem not_contains {D K : Addr} {c i : Nat}
    (hs : ∀ j < c, ∀ k < c, D + BitVec.ofNat 64 j ≠ K + BitVec.ofNat 64 k) (hi : i < c)
    (h : (⟨D, c⟩ : Region).Contains (K + BitVec.ofNat 64 i) 1) : False := by
  simp only [Region.Contains] at h
  refine hs (K + BitVec.ofNat 64 i - D).toNat (by omega) i hi ?_
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]

set_option simprocs false in
theorem byte_step {s : State} {D K : Addr} {c i : Nat} (hp : BPre s D K c) (hi : i < c) {s₁ : State}
    (h : LInv s D K c i s₁) :
    WP isa (.block xorBody) s₁ fun s' =>
      LInv s D K c (i + 1) s' ∧ s'.zf = some (decide (i + 1 = c)) := by
  have hc := hp.c_lt
  have ea₁ : D + BitVec.ofNat 64 i * BitVec.ofNat 64 1 + BitVec.ofInt 64 0 = D + BitVec.ofNat 64 i := by simp
  have ea₂ : K + BitVec.ofNat 64 i * BitVec.ofNat 64 1 + BitVec.ofInt 64 0 = K + BitVec.ofNat 64 i := by simp
  have i₁ : InRegions (s₁.rd ++ s₁.wr) (D + BitVec.ofNat 64 i) 1 := by
    obtain ⟨r, hr, hc⟩ := hp.wD i hi; exact ⟨r, by rw [h.rd, h.wr]; exact List.mem_append_right _ hr, hc⟩
  have i₂ : InRegions (s₁.rd ++ s₁.wr) (K + BitVec.ofNat 64 i) 1 := by rw [h.rd, h.wr]; exact hp.rK i hi
  have o₁ : InRegions s₁.wr (D + BitVec.ofNat 64 i) 1 := by rw [h.wr]; exact hp.wD i hi
  have hrbp : s₁.gpr .rbp = D := by rw [h.keep _ (by decide) (by decide) (by decide), hp.rbp]
  have hrsi : s₁.gpr .rsi = K := by rw [h.keep _ (by decide) (by decide) (by decide), hp.rsi]
  have hrdx : s₁.gpr .rdx = BitVec.ofNat 64 c := by rw [h.keep _ (by decide) (by decide) (by decide), hp.rdx]
  apply WP.of_runBlock
  simp (config := {decide := true}) only [xorBody, dataByte, ksByte, runBlock_cons, runStep_some,
    runBlock_nil, exec, State.ea, readSrc, execAlu, arithFlags, State.load8, State.store8,
    State.setReg, State.setFlags, hrbp, hrsi, h.rcx, ea₁, ea₂, i₁, i₂, o₁, ite_true, ite_false,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left', se1]
  have hd : s₁.mem (D + BitVec.ofNat 64 i) = s.mem (D + BitVec.ofNat 64 i) := by
    rw [h.data _ hi]; simp
  have hk : s₁.mem (K + BitVec.ofNat 64 i) = s.mem (K + BitVec.ofNat 64 i) :=
    h.frame _ fun r hr hcont => by
      simp only [List.mem_singleton] at hr; subst hr
      exact not_contains hp.sep hi hcont
  rw [hd, hk, xor_setWidth]
  refine ⟨⟨by simp [BitVec.ofNat_add], fun r h₁ h₂ h₃ => ?_, h.rd, h.wr, fun k hk' => ?_,
    h.frame.writeW (List.mem_singleton_self _) _ (contains_byte hi hc)⟩, ?_⟩
  · simp only [h₁, h₂, h₃, ite_false]; exact h.keep r h₁ h₂ h₃
  · dsimp only; rw [writeW8_apply]
    by_cases he : k = i
    · subst he; simp
    · simp only [D_ne hc hk' hi he, ite_false]
      rw [h.data k hk']
      by_cases h₁ : k < i
      · simp [h₁, show k < i + 1 by omega]
      · simp [h₁, show ¬ k < i + 1 by omega]
  · rw [hrdx, ← Offset.ofNat_sub_ofNat_beq (x := i + 1) (y := c) (by omega) (by omega), BitVec.ofNat_add]
    rfl


theorem loop_ok {s : State} {D K : Addr} {c : Nat} (hp : BPre s D K c) (hc0 : 0 < c) {s₁ : State}
    (h : LInv s D K c 0 s₁) : WP isa xorLoop s₁ (LInv s D K c c) := by
  rw [xorLoop_eq]
  let Inv : Nat → State → Prop := fun n s' => ∃ i, n = c - i ∧ i < c ∧ LInv s D K c i s'
  have hstep : ∀ n s', Inv n s' → WP isa (.block xorBody) s' (fun s'' =>
      (eval .ne s'' = some false ∧ LInv s D K c c s'') ∨ (eval .ne s'' = some true ∧ ∃ n' < n, Inv n' s'')) := by
    rintro n s' ⟨i, rfl, hi, hI⟩
    refine WP.mono (byte_step hp hi hI) fun s'' ⟨h', hz⟩ => ?_
    by_cases hl : i + 1 = c
    · exact .inl ⟨by simp [eval, hz, hl], hl ▸ h'⟩
    · exact .inr ⟨by simp [eval, hz, hl], c - (i + 1), by omega, i + 1, rfl, by omega, h'⟩
  exact WP.loop (M := isa) Inv hstep c s₁ ⟨0, by simp, hc0, h⟩

theorem xorBytes_eq : xorBytes =
    .seq (.block [.mov32 .rcx (.imm 0), .alu .test .rdx (.reg .rdx)])
      (.seq (.ite .e (.block []) xorLoop) (.block [.alu .add .rbp (.reg .rdx), .alu .sub .r12 (.reg .rdx)])) :=
  rfl

set_option simprocs false in
theorem xorBytes_ok {s : State} {D K : Addr} {c : Nat} (hp : BPre s D K c) :
    WP isa xorBytes s (BPost s D K c) := by
  have hc := hp.c_lt
  have h₁ : WP isa (.block [.mov32 .rcx (.imm 0), .alu .test .rdx (.reg .rdx)]) s fun s₁ =>
      LInv s D K c 0 s₁ ∧ s₁.zf = some (decide (c = 0)) := by
    apply WP.of_runBlock
    simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
      readSrc32, execAlu, arithFlags, State.setReg, State.setReg32, State.setFlags, Option.map_some,
      Option.bind_some, Option.some.injEq, exists_eq_left', ite_false]
    refine ⟨⟨by simp, fun r h₁ h₂ h₃ => by simp [h₃], rfl, rfl, fun k hk => by simp, Frame.refl _ _⟩, ?_⟩
    rw [BitVec.and_self, hp.rdx, ← Offset.ofNat_sub_ofNat_beq (x := c) (y := 0) (by omega) (by omega)]
    simp
  rw [xorBytes_eq]
  refine WP.seq (WP.mono h₁ fun s₁ ⟨hI, hz⟩ => ?_)
  refine WP.seq (WP.mono (Q := LInv s D K c c) ?_ fun s₂ h₂ => ?_)
  · refine WP.ite (decide (c = 0)) (by simp [eval, hz]) (fun h0 => WP.block_nil (M := isa) ?_) (fun h0 => loop_ok hp ?_ hI)
    · simp only [decide_eq_true_eq] at h0; subst h0; exact hI
    · simp only [decide_eq_false_iff_not] at h0; omega
  · have hrdx : s₂.gpr .rdx = BitVec.ofNat 64 c := by rw [h₂.keep _ (by decide) (by decide) (by decide), hp.rdx]
    have hrbp : s₂.gpr .rbp = D := by rw [h₂.keep _ (by decide) (by decide) (by decide), hp.rbp]
    have hr12 : s₂.gpr .r12 = s.gpr .r12 := h₂.keep _ (by decide) (by decide) (by decide)
    apply WP.of_runBlock
    simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
      execAlu, arithFlags, State.setReg, State.setFlags, Option.bind_some,
      Option.some.injEq, exists_eq_left', ite_false, hrdx, hrbp, hr12]
    refine ⟨by simp (config := {decide := true}), by simp (config := {decide := true}),
      fun r e₁ e₂ e₃ e₄ e₅ => ?_, h₂.rd, h₂.wr, fun k hk => ?_, h₂.frame⟩
    · simp only [e₄, e₅, ite_false]; exact h₂.keep r e₁ e₂ e₃
    · rw [h₂.data k hk, ite_pos hk]

end VG.Proof.ChaCha20.X86_64.Stream
