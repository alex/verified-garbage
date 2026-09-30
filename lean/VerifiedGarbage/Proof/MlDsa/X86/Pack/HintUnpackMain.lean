import VerifiedGarbage.Proof.MlDsa.X86.Pack.HintUnpackLoop

/-!
# ML-DSA on x86 (32-bit): `vg_mldsa_hint_bit_unpack`

Untrusted: everything here is checked by Lean. The polynomials
(`poly_piece`: the bound `y[ω + i]`, its two checks, and the coefficients
of `HintUnpackLoop.lean`), the bytes from the index up to `ω`
(`trail_piece`), and the return value (`ret_piece`), which is 1 iff no check
failed; `hintBitUnpack_eq` (`Pack/Hint.lean`) gives the contract.
-/

namespace VG.Proof.MlDsa.X86.Pack.Hint

open VG VG.X86 VG.Impl.MlDsa.X86.Pack
open VG.Impl.MlKem.X86 (at_ saveRegs)
open VG.Proof.MlKem.X86
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlDsa.Pack

namespace Up

/-- `OM`, after a block that writes only the registers `rs` (among `ebx`,
`edx` and `ebp`) and not memory. -/
theorem OM.keep {s₀ s s' : State} {i : Nat} {o : Option (Array (Vector Bool n) × Nat)} (h : OM s₀ i o s)
    {rs : List Reg} (k : Keep rs s s') (hrs : ∀ r ∈ rs, r = .ebx ∨ r = .edx ∨ r = .ebp) (hm : s'.mem = s.mem) :
    OM s₀ i o s' :=
  ⟨h.toPtr.keep k (fun r hr => by rcases hrs r hr with e | e | e <;> simp [e]) hm,
    by rw [k.gpr (fun hr => by rcases hrs _ hr with e | e | e <;> cases e), h.eax], by rw [hm]; exact h.sr⟩

/-! ## A polynomial -/

theorem q1_piece (i : Nat) : Piece Pre Pub (fun s₀ s => OM s₀ i (PS s₀ i) s ∧ i < K s₀)
    (fun s₀ s => (OM s₀ i (PS s₀ i) s ∧ i < K s₀) ∧ s.gpr .edx = arg s₀ 0 + BitVec.ofNat 32 (ω s₀ + i))
    (.block [.mov .edx (.mem (at_ .esp 36))]) := by
  refine Piece.taint [.esp] (fun s₀ s hp ⟨h, hi⟩ => ?_) (fun s₀ s₀' s s' _ _ hq ⟨h, _⟩ ⟨h', _⟩ r hr => ?_)
    (by taint_decide)
  · have a4 : addr (s.gpr .esp) 36 = argAddr s₀ 4 := argEa h.esp 4
    have i4 := h.argIn hp (i := 4) (by omega)
    have hb : WP isa (.block [.mov .edx (.mem (at_ .esp 36))]) s fun s' =>
        s'.gpr .edx = arg s₀ 0 + BitVec.ofNat 32 (ω s₀ + i) ∧ s'.mem = s.mem := by
      hrun [a4, i4, h.ptr]
    exact (WP.keep [.edx] hb (by decide)).mono fun s' ⟨⟨e, m⟩, k⟩ =>
      ⟨⟨h.keep k (by simp) m, hi⟩, e⟩
  · simp only [List.mem_singleton] at hr
    subst hr
    rw [h.esp, h'.esp, P0_esp, P0_esp, hq.e0]

theorem q2_piece (i : Nat) : Piece Pre Pub
    (fun s₀ s => (OM s₀ i (PS s₀ i) s ∧ i < K s₀) ∧ s.gpr .edx = arg s₀ 0 + BitVec.ofNat 32 (ω s₀ + i))
    (fun s₀ s => ((OM s₀ i (PS s₀ i) s ∧ i < K s₀) ∧ s.gpr .ebx = BitVec.ofNat 32 (bnd s₀ i)) ∧
      isa.eval .b s = some (decide (bnd s₀ i < idxOf (PS s₀ i))))
    (.block [.movzx8 .ebx (at_ .edx 0), .alu .cmp .ebx (.reg .eax)]) := by
  refine Piece.taint [.edx] (fun s₀ s hp ⟨⟨h, hi⟩, hd⟩ => ?_)
    (fun s₀ s₀' s s' _ _ hq ⟨_, hd⟩ ⟨_, hd'⟩ r hr => ?_) (by taint_decide)
  · have hf := hp.facts
    have hy : ω s₀ + i < yL s₀ := by omega
    have ea : addr (s.gpr .edx) 0 = rA s₀ + BitVec.ofNat 64 (ω s₀ + i) := by rw [hd]; exact yAddr hp hy
    have hin := h.inY hp hy
    have hv := h.ybyte hp hy
    have hb : WP isa (.block [.movzx8 .ebx (at_ .edx 0), .alu .cmp .ebx (.reg .eax)]) s fun s' =>
        s'.gpr .ebx = BitVec.setWidth 32 ((Y s₀).getD (ω s₀ + i) 0) ∧
        s'.cf = some (decide ((BitVec.setWidth 32 ((Y s₀).getD (ω s₀ + i) 0)).toNat < (s.gpr .eax).toNat)) ∧
        s'.mem = s.mem := by
      hrun [ea, hin, hv]
    have hl := idxOf_le hp h.sr
    refine (WP.keep [.ebx] hb (by decide)).mono fun s' ⟨⟨e, c, m⟩, k⟩ =>
      ⟨⟨⟨h.keep k (by simp) m, hi⟩, by rw [e, byte32]⟩, ?_⟩
    show s'.cf = _
    rw [c, toNat_setWidth32_8, h.eax, toNat_ofNat32 (by omega)]
  · simp only [List.mem_singleton] at hr
    subst hr
    rw [hd, hd', hq.a0, hq.eω]

theorem fail1_piece (i : Nat) : Piece Pre Pub
    (fun s₀ s => (((OM s₀ i (PS s₀ i) s ∧ i < K s₀) ∧ s.gpr .ebx = BitVec.ofNat 32 (bnd s₀ i)) ∧
      isa.eval .b s = some (decide (bnd s₀ i < idxOf (PS s₀ i)))) ∧ decide (bnd s₀ i < idxOf (PS s₀ i)) = true)
    (fun s₀ s => OM s₀ i (PS s₀ (i + 1)) s) hbuFail := by
  refine Piece.taint [] (fun s₀ s hp ⟨⟨⟨⟨h, _⟩, _⟩, _⟩, hb⟩ => ?_)
    (fun _ _ _ _ _ _ _ _ _ r hr => absurd hr (by simp)) (by taint_decide)
  have e := PS_fail₁ (of_decide_eq_true hb)
  have hbk : WP isa hbuFail s fun s' => s'.gpr .eax = 256 ∧ s'.mem = s.mem := by hrun [hbuFail]
  exact (WP.keep [.eax] hbk (by decide)).mono fun s' ⟨⟨e1, m⟩, k⟩ =>
    ⟨h.toPtr.keep k (fun r hr => by simp at hr; simp [hr]) m, by rw [e1, e]; rfl, by rw [e]; exact SR.none _ _⟩

theorem q3_piece (i : Nat) : Piece Pre Pub
    (fun s₀ s => (((OM s₀ i (PS s₀ i) s ∧ i < K s₀) ∧ s.gpr .ebx = BitVec.ofNat 32 (bnd s₀ i)) ∧
      isa.eval .b s = some (decide (bnd s₀ i < idxOf (PS s₀ i)))) ∧ decide (bnd s₀ i < idxOf (PS s₀ i)) = false)
    (fun s₀ s => (((OM s₀ i (PS s₀ i) s ∧ i < K s₀) ∧ s.gpr .ebx = BitVec.ofNat 32 (bnd s₀ i)) ∧
      ¬ bnd s₀ i < idxOf (PS s₀ i)) ∧ isa.eval .b s = some (decide (ω s₀ < bnd s₀ i)))
    (.block [.mov .edx (.mem (at_ .esp 28)), .alu .cmp .edx (.reg .ebx)]) := by
  refine Piece.taint [.esp] (fun s₀ s hp ⟨⟨⟨⟨h, hi⟩, he⟩, _⟩, hb⟩ => ?_)
    (fun s₀ s₀' s s' _ _ hq ⟨⟨⟨⟨h, _⟩, _⟩, _⟩, _⟩ ⟨⟨⟨⟨h', _⟩, _⟩, _⟩, _⟩ r hr => ?_) (by taint_decide)
  · have a2 : addr (s.gpr .esp) 28 = argAddr s₀ 2 := argEa h.esp 2
    have i2 := h.argIn hp (i := 2) (by omega)
    have v2 := h.argw hp (i := 2) (by omega) (by omega) (by omega)
    have hb' : WP isa (.block [.mov .edx (.mem (at_ .esp 28)), .alu .cmp .edx (.reg .ebx)]) s fun s' =>
        s'.cf = some (decide ((arg s₀ 2).toNat < (s.gpr .ebx).toNat)) ∧ s'.mem = s.mem := by
      hrun [a2, i2, v2]
    have := bnd_lt s₀ i
    refine (WP.keep [.edx] hb' (by decide)).mono fun s' ⟨⟨c, m⟩, k⟩ =>
      ⟨⟨⟨⟨h.keep k (by simp) m, hi⟩, by rw [k.gpr (by decide), he]⟩, of_decide_eq_false hb⟩, ?_⟩
    show s'.cf = _
    rw [c, he, toNat_ofNat32 (by omega)]
  · simp only [List.mem_singleton] at hr
    subst hr
    rw [h.esp, h'.esp, P0_esp, P0_esp, hq.e0]

theorem fail2_poly_piece (i : Nat) : Piece Pre Pub
    (fun s₀ s => ((((OM s₀ i (PS s₀ i) s ∧ i < K s₀) ∧ s.gpr .ebx = BitVec.ofNat 32 (bnd s₀ i)) ∧
      ¬ bnd s₀ i < idxOf (PS s₀ i)) ∧ isa.eval .b s = some (decide (ω s₀ < bnd s₀ i))) ∧
      decide (ω s₀ < bnd s₀ i) = true)
    (fun s₀ s => OM s₀ i (PS s₀ (i + 1)) s) hbuFail := by
  refine Piece.taint [] (fun s₀ s hp ⟨⟨⟨⟨⟨h, _⟩, _⟩, _⟩, _⟩, hb⟩ => ?_)
    (fun _ _ _ _ _ _ _ _ _ r hr => absurd hr (by simp)) (by taint_decide)
  have e := PS_fail₂ (of_decide_eq_true hb)
  have hbk : WP isa hbuFail s fun s' => s'.gpr .eax = 256 ∧ s'.mem = s.mem := by hrun [hbuFail]
  exact (WP.keep [.eax] hbk (by decide)).mono fun s' ⟨⟨e1, m⟩, k⟩ =>
    ⟨h.toPtr.keep k (fun r hr => by simp at hr; simp [hr]) m, by rw [e1, e]; rfl, by rw [e]; exact SR.none _ _⟩

theorem coefs_poly_piece (i : Nat) : Piece Pre Pub
    (fun s₀ s => ((((OM s₀ i (PS s₀ i) s ∧ i < K s₀) ∧ s.gpr .ebx = BitVec.ofNat 32 (bnd s₀ i)) ∧
      ¬ bnd s₀ i < idxOf (PS s₀ i)) ∧ isa.eval .b s = some (decide (ω s₀ < bnd s₀ i))) ∧
      decide (ω s₀ < bnd s₀ i) = false)
    (fun s₀ s => OM s₀ i (PS s₀ (i + 1)) s) hbuCoefs :=
  (coefs_piece i).mono (fun s₀ s _ ⟨⟨⟨⟨⟨h, hi⟩, he⟩, h1⟩, _⟩, hb⟩ => by
      have h2 := of_decide_eq_false hb
      obtain ⟨e1, e2, -⟩ := PS_ok h1 h2
      have eG : G s₀ i 0 = PS s₀ i := by rw [e1]; rfl
      exact ⟨h.toPtr, he, by rw [eG]; exact h.eax, by rw [eG]; exact h.sr, hi, e1, e2, by omega⟩)
    fun s₀ s _ h => by
      obtain ⟨-, -, e3⟩ := PS_ok (s₀ := s₀) (i := i) (by rw [h.some]; exact Nat.not_lt.mpr h.fb)
        (Nat.not_lt.mpr h.bw)
      exact ⟨h.toPtr, by rw [e3]; exact h.eax, by rw [e3]; exact h.sr⟩

theorem end_piece (i : Nat) : Piece Pre Pub (fun s₀ s => OM s₀ i (PS s₀ (i + 1)) s ∧ i < K s₀)
    (fun s₀ s => OM s₀ (i + 1) (PS s₀ (i + 1)) s ∧ isa.eval .ne s = some (decide (i + 1 < K s₀)))
    (.block hbuPolyEnd) := by
  refine Piece.taint [.esp] (fun s₀ s hp ⟨h, hi⟩ => ?_) (fun s₀ s₀' s s' _ _ hq ⟨h, _⟩ ⟨h', _⟩ r hr => ?_)
    (by taint_decide)
  · have hf := hp.facts
    have a1 : addr (s.gpr .esp) 24 = argAddr s₀ 1 := argEa h.esp 1
    have a4 : addr (s.gpr .esp) 36 = argAddr s₀ 4 := argEa h.esp 4
    have i1 := h.argIn hp (i := 1) (by omega)
    have i4 := h.argIn hp (i := 4) (by omega)
    have o1 := h.argOut hp (i := 1) (by omega)
    have o4 := h.argOut hp (i := 4) (by omega)
    have s14 : Mem.Sep (argAddr s₀ 1) (32 / 8) (argAddr s₀ 4) (32 / 8) :=
      (hp.slot_disj (i := 1) (j := 4) (by omega) (by omega) (by omega)).sep (Region.contains_self _ _)
        (Region.contains_self _ _)
    have s41 : Mem.Sep (argAddr s₀ 4) (32 / 8) (argAddr s₀ 1) (32 / 8) :=
      (hp.slot_disj (i := 4) (j := 1) (by omega) (by omega) (by omega)).sep (Region.contains_self _ _)
        (Region.contains_self _ _)
    have r1 : ∀ v : BitVec 32, (s.mem.writeW (argAddr s₀ 4) v).readW (argAddr s₀ 1) 32 =
        BitVec.ofNat 32 (K s₀ - i) := fun v => by rw [Mem.readW_writeW_sep s14 (by decide), h.cnt]
    have hb : WP isa (.block hbuPolyEnd) s fun s' => s'.gpr .ecx = s.gpr .ecx + 1024 ∧
        s'.zf = some (BitVec.ofNat 32 (K s₀ - i) - 1 == 0) ∧
        s'.mem = (s.mem.writeW (argAddr s₀ 4) (arg s₀ 0 + BitVec.ofNat 32 (ω s₀ + i) + 1)).writeW (argAddr s₀ 1)
          (BitVec.ofNat 32 (K s₀ - i) - 1) := by
      hrun [hbuPolyEnd, a1, a4, i1, i4, o1, o4, h.ptr, r1]
    refine (WP.keep [.edx, .ecx] hb (by decide)).mono fun s' ⟨⟨e1, z, m⟩, k⟩ => ⟨⟨⟨h.toBase.keep k (by decide)
      (by rw [m]; exact (frame_slot (.inr rfl) _).trans (frame_slot (.inl rfl) _)),
      by rw [k.gpr (by decide), h.edi], by rw [k.gpr (by decide), h.esi], by rw [e1, h.ecx, add_1024']; congr 2,
      ?_, ?_⟩, by rw [k.gpr (by decide), h.eax], ?_⟩, eval_ne_cnt hi (by omega) z⟩
    · rw [m, Mem.readW_writeW_self32]; exact cnt_next hi
    · rw [m, Mem.readW_writeW_sep s41 (by decide), Mem.readW_writeW_self32, add_one']; rfl
    · rw [m]
      exact h.sr.congr fun t ht => by rw [hp.coeff_frame (by omega) _ t ht, hp.coeff_frame (by omega) _ t ht]
  · simp only [List.mem_singleton] at hr
    subst hr
    rw [h.esp, h'.esp, P0_esp, P0_esp, hq.e0]

theorem poly_piece (i : Nat) : Piece Pre Pub (fun s₀ s => OM s₀ i (PS s₀ i) s ∧ i < K s₀)
    (fun s₀ s => OM s₀ (i + 1) (PS s₀ (i + 1)) s ∧ isa.eval .ne s = some (decide (i + 1 < K s₀)))
    (.seq hbuPoly (.block hbuPolyEnd)) := by
  refine Piece.seq (addX (X := fun s₀ => i < K s₀) ?_ fun _ _ _ h => h.2) ((end_piece i).mono (fun _ _ _ h => h)
    fun _ _ _ h => h)
  refine Piece.seq (q1_piece i) (Piece.seq (q2_piece i) (Piece.ite
    (fun s₀ => decide (bnd s₀ i < idxOf (PS s₀ i))) (fun _ _ _ h => h.2)
    (fun s₀ s₀' _ _ hq => by rw [hq.ebnd, hq.ePS]) (fail1_piece i) (Piece.seq (q3_piece i) (Piece.ite
      (fun s₀ => decide (ω s₀ < bnd s₀ i)) (fun _ _ _ h => h.2)
      (fun s₀ s₀' _ _ hq => by rw [hq.ebnd, hq.eω]) (fail2_poly_piece i) (coefs_poly_piece i)))))

theorem polys_piece : Piece Pre Pub (fun s₀ s => OM s₀ 0 (PS s₀ 0) s) (fun s₀ s => OM s₀ (K s₀) (PS s₀ (K s₀)) s)
    (.loop (.seq hbuPoly (.block hbuPolyEnd)) .ne) :=
  loopN (fun i s₀ s => OM s₀ i (PS s₀ i) s) K (fun s₀ hp => by have := hp.facts; omega)
    (fun _ _ _ _ hq => hq.eK) poly_piece

end Up

end VG.Proof.MlDsa.X86.Pack.Hint
