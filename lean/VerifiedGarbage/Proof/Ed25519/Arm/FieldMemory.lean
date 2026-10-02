import VerifiedGarbage.Impl.Ed25519.Arm.Field
import VerifiedGarbage.Proof.Ed25519.Arm.Slots

/-! Constants and copies in the sixteen-limb field workspace. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem slot_range (o : Slot) : 64 ≤ offset o ∧ offset o + 64 ≤ ACC := by
  simp only [offset, ACC]
  omega

theorem slot_sep (o a : Slot) :
    offset o = offset a ∨ offset o + 64 ≤ offset a ∨ offset a + 64 ≤ offset o := by
  simp only [offset]
  omega

/-- A prefix of sixteen independent limb stores. -/
structure FillInv (b : BitVec 32) (o : Nat) (s0 : State) (f : Nat → Nat) (k : Nat)
    (s : State) (ws : List Reg := [.r3]) : Prop where
  rest : Rest ws s0 s
  frame : Frame [⟨State.addr b + BitVec.ofNat 64 o, 4 * k⟩] s0.mem s.mem
  outs : ∀ j < k, limb s.mem (State.addr b) o j = f j

theorem fill_regs_ok {ws : List Reg} (h0 : Reg.r0 ∉ ws) {b : BitVec 32} {o : Nat} {src : Nat → List Instr} {s0 : State}
    {f : Nat → Nat} (hc : Ctx b s0) (ho : o + 64 ≤ 4096)
    (hsrc : ∀ k < 16, ∀ s, FillInv b o s0 f k s ws →
      WP isa (.block (src k)) s fun t =>
        (t.gpr .r3).toNat = f k ∧ Rest ws s t ∧ t.mem = s.mem) :
    WP isa (.block ((List.range 16).flatMap fun k =>
      src k ++ ([.str .r3 .r0 (o + 4 * k)] : List Instr))) s0 (fun t => FillInv b o s0 f 16 t ws) := by
  refine wp_range_flatMap (M := isa) (fun k t => FillInv b o s0 f k t ws) (fun k s hk h => ?_)
    16 (Nat.le_refl _) s0 ⟨Rest.refl _ _, Frame.refl _ _, fun j hj => by omega⟩
  refine WP.append (hsrc k hk s h) fun t ⟨hv, hr, hm⟩ => ?_
  refine str0_ok ((hc.of_rest h.rest h0).of_rest hr h0)
    (by omega) fun u hu => WP.block_nil ?_
  have em : u.mem = s.mem.writeW (State.addr b + BitVec.ofNat 64 (o + 4 * k))
      (t.gpr .r3) := by rw [hu.mem, hm]
  refine ⟨h.rest.trans (hr.trans (hu.rest _)), ?_, fun j hj => ?_⟩
  · rw [em]
    refine (h.frame.sub fun r hmem => ⟨_, List.mem_singleton_self _, ?_⟩).writeW
      (List.mem_singleton_self _) _ (Offset.contains _ (Nat.le_add_right _ _)
        (by omega) (by omega))
    rw [List.mem_singleton.mp hmem]
    exact Region.sub_prefix (by omega)
  · rw [limb, em]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [wd_write_other _ _ _ (by omega) (by omega) (by omega)]
      exact h.outs j hj
    · rw [wd_write_self, hv]

theorem fill_ok {b : BitVec 32} {o : Nat} {src : Nat → List Instr} {s0 : State}
    {f : Nat → Nat} (hc : Ctx b s0) (ho : o + 64 ≤ 4096)
    (hsrc : ∀ k < 16, ∀ s, FillInv b o s0 f k s →
      WP isa (.block (src k)) s fun t =>
        (t.gpr .r3).toNat = f k ∧ Rest [.r3] s t ∧ t.mem = s.mem) :
    WP isa (.block ((List.range 16).flatMap fun k =>
      src k ++ ([.str .r3 .r0 (o + 4 * k)] : List Instr))) s0 (FillInv b o s0 f 16) :=
  fill_regs_ok (by decide) hc ho hsrc

theorem val16_digits (v n : Nat) :
    val16 (fun k => v / 2 ^ (16 * k) % 65536) n = v % 2 ^ (16 * n) := by
  induction n with
  | zero => simp only [val16, Nat.mul_zero, Nat.pow_zero, Nat.mod_one]
  | succ n ih =>
    rw [val16_succ, ih, pow16_succ, Nat.mod_mul]

theorem constField_op {b : BitVec 32} {s : State} (hc : Ctx b s) (o : Slot)
    (v : Spec.X25519.Fe) :
    WP isa (.block (constField o v)) s fun t =>
      Rest [.r3] s t ∧ Frame [⟨State.addr b + BitVec.ofNat 64 (offset o), 64⟩] s.mem t.mem ∧
      Lim t.mem (State.addr b) (offset o) ∧ FS t.mem (State.addr b) (offset o) = v := by
  have ho := slot_range o
  refine WP.mono (fill_ok (src := fun k => [.movw .r3 (BitVec.ofNat 16 (v.val / 2 ^ (16 * k)))])
    (f := fun k => v.val / 2 ^ (16 * k) % 65536) hc (by rw [ACC_eq] at ho; omega)
    (fun k _ t _ => wp_movw fun u hu => WP.block_nil ⟨?_, hu.rest (by decide), hu.mem⟩))
    fun t ht => ⟨ht.rest, ht.frame, ?_, ?_⟩
  · rw [hu.gpr, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    exact Nat.lt_trans (Nat.mod_lt _ (by decide : 0 < 2 ^ 16)) (by decide)
  · intro k hk
    rw [ht.outs k hk]
    exact Nat.mod_lt _ (by decide)
  · rw [FS, V, val16_congr ht.outs, val16_digits, Nat.mod_eq_of_lt]
    · exact VG.Proof.X25519.toFe_self v
    · have := v.isLt
      simp only [Spec.X25519.P] at this
      omega

theorem copyField_op {b : BitVec 32} {s : State} (hc : Ctx b s) (o a : Slot)
    (hl : Lim s.mem (State.addr b) (offset a)) :
    WP isa (.block (copyField o a)) s fun t =>
      Rest [.r3] s t ∧ Frame [⟨State.addr b + BitVec.ofNat 64 (offset o), 64⟩] s.mem t.mem ∧
      Lim t.mem (State.addr b) (offset o) ∧
      FS t.mem (State.addr b) (offset o) = FS s.mem (State.addr b) (offset a) := by
  have ho := slot_range o
  have ha := slot_range a
  have hsep := slot_sep o a
  rw [ACC_eq] at ho ha
  refine WP.mono (fill_ok (src := fun k => [.ldr .r3 .r0 (offset a + 4 * k)])
    (f := limb s.mem (State.addr b) (offset a)) hc (by omega)
    (fun k hk t ht => ldr0_ok (hc.of_rest ht.rest (by decide)) (by omega)
      fun u hu => WP.block_nil ⟨?_, hu.rest (by decide), hu.mem⟩))
    fun t ht => ⟨ht.rest, ht.frame, ?_, ?_⟩
  · rw [hu.gpr]
    exact wd_frame ht.frame fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact Offset.disjoint _ (by omega) (by omega) (by omega)
  · intro k hk
    rw [ht.outs k hk]
    exact hl k hk
  · exact congrArg VG.Proof.X25519.toFe (val16_congr ht.outs)

end VG.Proof.Ed25519.Arm
