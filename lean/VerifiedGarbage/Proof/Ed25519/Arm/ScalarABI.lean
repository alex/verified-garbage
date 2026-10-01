import VerifiedGarbage.Impl.Ed25519.Arm.ScalarABI
import VerifiedGarbage.Proof.Ed25519.Arm.Field

/-! Saving and restoring the callee-saved registers in the reviewed scratch buffer. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

/-- The registers `g` saved at `[0, 32)` of the working space at `B`. -/
def ScalarSaved (B : Addr) (g : Reg → BitVec 32) (m : Mem) : Prop :=
  ∀ i < 8, m.readW (B + BitVec.ofNat 64 (4 * i)) 32 = g (scalarSavedReg i)

section
variable {b : BitVec 32}

theorem scalarSave_ok {s : State} {base : Reg} (h3 : s.gpr base = b) (hfit : b.toNat + 8192 ≤ 2 ^ 32)
    (hw : (⟨State.addr b, 8192⟩ : Region) ∈ s.wr) :
    WP isa (.block (scalarSave base)) s fun s' =>
      ScalarSaved (State.addr b) s.gpr s'.mem ∧ Frame [⟨State.addr b, 32⟩] s.mem s'.mem ∧ s'.gpr = s.gpr ∧
        Rest [] s s' := by
  refine WP.mono (wp_range_flatMap (M := isa)
    (fun n s' => (∀ i < n, s'.mem.readW (State.addr b + BitVec.ofNat 64 (4 * i)) 32 = s.gpr (scalarSavedReg i)) ∧
      Frame [⟨State.addr b, 4 * n⟩] s.mem s'.mem ∧ s'.gpr = s.gpr ∧ Rest [] s s')
    (fun n s' hn ⟨h1, h2, h3', h4⟩ => ?_) 8 (Nat.le_refl _) s
    ⟨fun _ h => absurd h (Nat.not_lt_zero _), Frame.refl _ _, rfl, Rest.refl _ _⟩)
    fun s' h => ⟨h.1, h.2.1, h.2.2⟩
  refine wp_str (a := State.addr b + BitVec.ofNat 64 (4 * n)) (by omega)
    (by rw [h3', h3]; exact addr_add (by omega)) (by rw [h4.wr]; exact in_base hw (by omega) (by omega))
    fun s2 u2 => WP.block_nil ⟨fun i hi => ?_, ?_, by rw [u2.gpr, h3'], h4.trans (u2.rest _)⟩
  · rw [u2.mem]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide)]; exact h1 i hi
    · rw [Mem.readW_writeW_self32, h3']
  · rw [u2.mem]
    exact (h2.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by omega)⟩).writeW
      (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))

theorem scalarRestore_ok {s : State} (hc : Ctx b s) {g : Reg → BitVec 32} (hs : ScalarSaved (State.addr b) g s.mem) :
    WP isa (.block scalarRestore) s fun s' => (∀ i < 8, s'.gpr (scalarSavedReg i) = g (scalarSavedReg i)) ∧
      Rest [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11] s s' ∧ s'.mem = s.mem := by
  have hsr : ∀ i < 8, scalarSavedReg i ∈ [Reg.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11] := by decide
  have hinj : ∀ i < 8, ∀ j < 8, scalarSavedReg i = scalarSavedReg j → i = j := by decide
  have h0 : ∀ i < 8, scalarSavedReg i ≠ .r0 := by decide
  refine WP.mono (wp_range_flatMap (M := isa)
    (fun n s' => (∀ i < n, s'.gpr (scalarSavedReg i) = g (scalarSavedReg i)) ∧
      Rest [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11] s s' ∧ s'.mem = s.mem)
    (fun n s' hn ⟨hl, hr, hm⟩ => ?_) 8 (Nat.le_refl _) s
    ⟨fun _ h => absurd h (Nat.not_lt_zero _), Rest.refl _ _, rfl⟩) fun s' h => h
  refine ldr0_ok (hc.of_rest hr (by decide)) (d := 4 * n) (by omega) fun s1 u1 =>
    WP.block_nil ⟨fun i hi => ?_, hr.trans (u1.rest (hsr n hn)), by rw [u1.mem, hm]⟩
  rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h' | rfl
  · rw [u1.other _ (fun e => absurd (hinj _ (by omega) _ hn e) (by omega))]; exact hl i h'
  · rw [u1.gpr, hm, hs i hn]

/-- The saved registers stay where no code writes. -/
theorem ScalarSaved.frame {g : Reg → BitVec 32} {m m' : Mem} (hs : ScalarSaved (State.addr b) g m) {rs : List Region}
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, ∀ i < 8, Region.Disjoint ⟨State.addr b + BitVec.ofNat 64 (4 * i), 4⟩ r) :
    ScalarSaved (State.addr b) g m' := fun i hi => by
  rw [hf.readW (Region.contains_self _ _) (fun r hr => hd r hr i hi) (by decide)]; exact hs i hi

end

end VG.Proof.Ed25519.Arm
