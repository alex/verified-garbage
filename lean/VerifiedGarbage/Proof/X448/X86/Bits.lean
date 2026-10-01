import VerifiedGarbage.Proof.X448.X86.Clamp

/-!
# X448 on x86 (32-bit): decoding the scalar bits

Untrusted: everything here is checked by Lean. The unrolled expansion
reads exactly 56 bytes, then clears bits zero and one and sets bit 447.
-/

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86 VG.Proof.X448

def bitRegs : List Reg := [.eax, .edx]

def expandBits : List Instr := (List.range 56).flatMap fun i =>
  [.movzx8 .eax (at_ .esi i)] ++ (List.range 8).flatMap (bitJ i)

theorem expandBits_ok {s : State} {base k : Addr} (hs : Scr s base)
    (hk : (s.gpr .esi).setWidth 64 = k) (hfit : (s.gpr .esi).toNat + 56 ≤ 2 ^ 32)
    (hr : ∀ i < 56, InRegions (s.rd ++ s.wr) (off k i) 1)
    (hd : ∀ i < 56, 8192 ≤ ofs base (off k i)) :
    WP isa (.block expandBits) s fun t =>
      Keeps bitRegs s t ∧ Outside base BITS 448 s.mem t.mem ∧
      ∀ j < 448, t.mem (off base (BITS + j)) =
        BitVec.ofNat 8 (((s.mem (off k (j / 8))).toNat >>> (j % 8)) &&& 1) := by
  let inv := fun n (t : State) => Keeps bitRegs s t ∧ Outside base BITS (8 * n) s.mem t.mem ∧
    ∀ j < 8 * n, t.mem (off base (BITS + j)) =
      BitVec.ofNat 8 (((s.mem (off k (j / 8))).toNat >>> (j % 8)) &&& 1)
  have step : ∀ n t, n < 56 → inv n t → WP isa (.block
      ([.movzx8 .eax (at_ .esi n)] ++ (List.range 8).flatMap (bitJ n))) t (inv (n + 1)) := by
    intro n t hn ⟨tk, tm, tb⟩
    have ea : t.ea (at_ .esi n) = off k n := by
      change addr (t.gpr .esi) n = _
      rw [tk.1 _ (by decide), addr_eq (by omega), hk]
    refine wp_load8 ea (by rw [tk.2.1, tk.2.2]; exact hr n hn) fun u hu => ?_
    have us := (hs.of_keeps tk (by decide)).of_upd hu (by decide)
    refine WP.mono (byteBits_ok us hn hu.gpr) fun v ⟨vb, vm, vk⟩ => ?_
    have byte : t.mem (off k n) = s.mem (off k n) :=
      tm _ (Or.inr (by have := hd n hn; simp only [BITS]; omega))
    refine ⟨tk.trans ((hu.rest (by decide)).trans (vk.mono (by simp [bitRegs]))), ?_, ?_⟩
    · rw [hu.mem] at vm
      exact (tm.mono (by omega) (by omega)).trans (vm.mono (by omega) (by omega))
    · intro j hj
      rcases Nat.lt_or_ge j (8 * n) with h | h
      · rw [vm _ (Or.inl (by rw [ofs_off' base (by simp only [BITS]; omega)]; omega)), hu.mem]
        exact tb j h
      · have e := vb (j - 8 * n) (by omega)
        rw [show 8 * n + (j - 8 * n) = j by omega, byte] at e
        rw [e, show j / 8 = n by omega, show j % 8 = j - 8 * n by omega]
  exact wp_range_flatMap (M := isa) (N := 56) inv step 56 (by decide) s
    ⟨Keeps.refl _ _, Outside.refl _ _ _ _, fun _ hj => by omega⟩

theorem getD_bytesAt (m : Mem) (k : Addr) {q : Nat} (hq : q < 56) :
    (Spec.X448.bytesAt m k 56).getD q 0 = m (k + BitVec.ofNat 64 q) := by
  simp only [Spec.X448.bytesAt, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range hq, Option.map_some, Option.getD_some]

/-- Expanded and clamped bytes are precisely the decoded scalar's bits. -/
theorem bitsData_ok {s : State} {base k : Addr} (hs : Scr s base)
    (hk : (s.gpr .esi).setWidth 64 = k) (hfit : (s.gpr .esi).toNat + 56 ≤ 2 ^ 32)
    (hr : ∀ i < 56, InRegions (s.rd ++ s.wr) (off k i) 1)
    (hd : ∀ i < 56, 8192 ≤ ofs base (off k i)) :
    WP isa (.block (expandBits ++ clamp)) s fun t =>
      (∀ r, r ∉ bitRegs → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      Outside base BITS 448 s.mem t.mem ∧
      ∀ j < 448, t.mem (off base (BITS + j)) =
        BitVec.ofNat 8 (bit (Spec.X448.decodeScalar448 (Spec.X448.bytesAt s.mem k 56)) j) := by
  rw [WP.block_append_iff]
  refine WP.mono (expandBits_ok hs hk hfit hr hd) fun s₂ ⟨k₂, o₂, b₂⟩ => ?_
  refine WP.mono (clamp_ok (hs.of_keeps k₂ (by decide))) fun s₃ ⟨m₃, k₃⟩ => ?_
  refine ⟨fun r hr => ?_, k₃.2.1.trans k₂.2.1, k₃.2.2.trans k₂.2.2, fun x hx => ?_, fun t ht => ?_⟩
  · rw [k₃.1 r (by intro he; simp only [List.mem_singleton] at he; subst r; exact hr (by decide))]
    exact k₂.1 r hr
  · rw [m₃, clampMem]
    have o : ∀ d, BITS ≤ d → d < BITS + 448 → ofs base x ≠ d := fun d h₁ h₂ h => by omega
    rw [writeW8_outside _ _ _ (by simp only [BITS]; omega) (o (BITS + 447) (by omega) (by omega)),
      writeW8_outside _ _ _ (by simp only [BITS]; omega) (o (BITS + 1) (by omega) (by omega)),
      writeW8_outside _ _ _ (by simp only [BITS]; omega) (o BITS (by omega) (by omega))]
    exact o₂ x hx
  · rw [m₃, clampMem, scalar_bit (length_bytesAt _ _ _) ht]
    simp (disch := simp only [BITS]; omega) only [writeW8_apply, off_eq_iff, Nat.add_left_cancel_iff,
      Nat.add_eq_left]
    rcases (by omega : t = 0 ∨ t = 1 ∨ t = 447 ∨ (2 ≤ t ∧ t < 447)) with
      rfl | rfl | rfl | ⟨h₃, h₄⟩
    · rfl
    · rfl
    · rfl
    · simp only [show t ≠ 447 by omega, show t ≠ 1 by omega, show t ≠ 0 by omega,
        show ¬t < 2 by omega, ite_false]
      rw [b₂ t (by omega), getD_bytesAt _ _ (by omega)]


end VG.Proof.X448.X86
