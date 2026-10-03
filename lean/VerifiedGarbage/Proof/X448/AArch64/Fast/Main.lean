import VerifiedGarbage.Proof.X448.AArch64.Fast.Finish
import VerifiedGarbage.Proof.X448.AArch64.Weak.Main

/-!
# X448 on AArch64: the whole function, with register-resident field arithmetic

Untrusted: everything here is checked by Lean.
-/

namespace VG.Proof.X448.AArch64.Fast

open VG VG.AArch64 VG.Proof.X448
open VG.Impl.X448.AArch64 (ld st slot SWAP BITS)
open VG.Proof.X448.AArch64 (Keeps Scr word off Outside Outside2 limbs FieldMem ofs Slot Saved Pre far
  far_output bytesAt_outside pointR scalarR outR scR bits_ok moveOutput_ok bitRegs)
open VG.Proof.X448.AArch64.Weak (Index Env E_outside cswap_fst invEnv invEnv_x2 invEnv_eval opSwap)
open VG.Impl.X448.AArch64.Fast (saved)

local notation "EV" => VG.Proof.X448.AArch64.Weak.E

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa Impl.X448.AArch64.Fast.x448 s₀ fun s' => (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧
      (∀ r ∈ preservedV, (s'.v r).extractLsb' 0 64 = (s₀.v r).extractLsb' 0 64) ∧
      Proof.X448.x448AArch64.post s₀ s' := by
  obtain ⟨base, hbase⟩ : ∃ b, s₀.gpr .x3 = b := ⟨_, rfl⟩
  have hn : base.toNat + 8192 ≤ 2 ^ 64 := hbase ▸ hp.sc_fit
  have hw₀ : (⟨base, 8192⟩ : Region) ∈ s₀.wr := by rw [hp.wr, ← hbase]; simp
  have hr : ∀ j < 56, InRegions (s₀.rd ++ s₀.wr) (off (s₀.gpr .x2) j) 1 := fun j hj =>
    ⟨pointR s₀, by rw [hp.rd]; simp, Offset.contains_base _ (by omega) (by omega)⟩
  have hd : ∀ j < 56, 8192 ≤ ofs base (off (s₀.gpr .x2) j) :=
    fun j hj => far (hbase ▸ hp.point_sc) hj (by decide)
  have kd : ∀ j < 56, 8192 ≤ ofs base (off (s₀.gpr .x1) j) :=
    fun j hj => far (hbase ▸ hp.scalar_sc) hj (by decide)
  rw [Impl.X448.AArch64.Fast.x448]
  refine WP.seq (WP.mono (setup_ok hbase hw₀ hn rfl hr hd)
    fun s₁ ⟨hs₁, b₁, r₁, savedOut₁, k₁, o₁, sv₁, svx₁, x1₁, x2₁, z2₁, x3₁, z3₁, sw₁, svV₁⟩ => ?_)
  have kr : ∀ j < 56, InRegions (s₁.rd ++ s₁.wr) (off (s₀.gpr .x1) j) 1 := fun j hj =>
    ⟨scalarR s₀, by rw [k₁.2.1, hp.rd]; simp, Offset.contains_base _ (by omega) (by omega)⟩
  refine WP.seq (WP.mono (bits_ok hs₁ (k₁.1 _ (by decide)) kr kd)
    fun s₂ ⟨g₂, rd₂, wr₂, o₂, bits₂⟩ => ?_)
  have k₂ : Keeps bitRegs s₁ s₂ := ⟨g₂, rd₂, wr₂⟩
  refine WP.seq (WP.mono (moveOutput_ok s₂) fun s₃ ⟨out₃, m₃, k₃⟩ => ?_)
  have k03 := k₁.then (k₂.then k₃)
  have hs₃ := (hs₁.of_keeps k₂ (by decide)).of_keeps k₃ (by decide)
  have sv₃ : Saved base s₀.gpr s₃.mem := by rw [m₃]; exact sv₁.outside o₂ (by decide)
  have svx₃ : SavedX base s₀.gpr s₃.mem := by
    rw [m₃]; exact svx₁.outside o₂ (by simp only [BITS, Impl.X448.AArch64.Fast.SAVE]; omega)
  have svV₃ : SavedV base s₀.v s₃.mem := by
    rw [m₃]; exact svV₁.outside o₂ (by simp only [BITS, Impl.X448.AArch64.Fast.VSAVE]; omega)
  have l₃ : ∀ i : Index, ∀ j < 8, limbs s₃.mem base (slot i.val) j = limbs s₁.mem base (slot i.val) j := by
    intro i j hj
    rw [m₃]
    exact o₂.limbs (Or.inl (by have := i.isLt; simp only [slot, BITS]; omega))
      (by have := i.isLt; simp only [slot]; omega) (by omega)
  have e₃ : ∀ i : Index, EV s₃.mem base i = EV s₁.mem base i := fun i =>
    congrArg toFe (VG.Proof.X448.Wide.valN_congr (l₃ i))
  have b₃ : BEnv s₃.mem base := fun i j hj => by rw [l₃ i j hj]; exact b₁ i j hj
  have kb := bytesAt_outside o₁ kd
  refine WP.seq (WP.mono (ladder_ok (s₀ := s₃) (s := s₃)
    (k := Spec.X448.decodeScalar448 (Spec.X448.bytesAt s₀.mem (s₀.gpr .x1) 56))
    (u := toFe (Spec.X448.decodeUCoordinate (Spec.X448.bytesAt s₀.mem (s₀.gpr .x2) 56)))
    (fun t ht => by rw [m₃, bits₂ t ht, kb])
    (fun s' hb hg hm hr hw => ⟨
      ⟨(hg _ (by decide)).trans hs₃.x3, (hg _ (by decide)).trans hs₃.mask, hw ▸ hs₃.wr, hn⟩, hm ▸ b₃,
      fun i _ j hj => by rw [hm, l₃ i j hj]; exact r₁ i j hj,
      ⟨fun r h => hg r (fun e => h (by subst r; exact List.mem_cons_self)), hr, hw⟩,
      hb, hm ▸ Outside2.refl _ _ _ _ _ _,
      by rw [hm, e₃ 0, x1₁], by rw [hm, e₃ 1, x2₁]; rfl,
      by rw [hm, e₃ 2, z2₁]; rfl, by rw [hm, e₃ 3, x3₁, x1₁]; rfl,
      by rw [hm, e₃ 4, z3₁]; rfl,
      by rw [hm, m₃, o₂.word (d := SWAP) (by decide) (by decide), sw₁]; rfl⟩)) fun s₄ L => ?_)
  refine WP.seq (WP.mono (lastSwap_ok L.scr L.env
    (by have := VG.Proof.X448.ladderAfter_swap_le
          (Spec.X448.decodeScalar448 (Spec.X448.bytesAt s₀.mem (s₀.gpr .x1) 56))
          (toFe (Spec.X448.decodeUCoordinate (Spec.X448.bytesAt s₀.mem (s₀.gpr .x2) 56)))
          (n := 0) (by decide); omega) L.swap) fun s₅ ⟨k₅, b₅, e₅⟩ => ?_)
  have hs₅ := k₅.scr L.scr
  refine WP.seq (WP.mono (invert_ok hs₅ b₅) fun s₆ ⟨k₆, b₆, e₆⟩ => ?_)
  have k36 := L.regs.then (k₅.regs.then k₆.regs)
  have sv₆ := ((sv₃.outside2 L.mem (by decide) (by decide)).outside2 k₅.mem (by decide)
    (by decide)).outside2 k₆.mem (by decide) (by decide)
  have svx₆ := ((svx₃.outside2 L.mem (by decide) (by decide)).outside2 k₅.mem (by decide)
    (by decide)).outside2 k₆.mem (by decide) (by decide)
  have svV₆ := ((svV₃.outside2 L.mem (by decide) (by decide)).outside2 k₅.mem (by decide)
    (by decide)).outside2 k₆.mem (by decide) (by decide)
  have out₆ : s₆.gpr .x1 = s₀.gpr .x0 :=
    (k36.1 _ (by decide)).trans (out₃.trans ((g₂ _ (by decide)).trans savedOut₁))
  have k06 := k03.then k36
  have hw₆ : ∀ j < 56, InRegions s₆.wr (off (s₀.gpr .x0) j) 1 := fun j hj =>
    ⟨outR s₀, by rw [k06.2.2, hp.wr]; simp, Offset.contains_base _ (by omega) (by omega)⟩
  refine WP.mono (finish_ok (k₆.scr hs₅) b₆ out₆ hw₆
    (fun j hj => far_output (hbase ▸ hp.out_sc) hj) sv₆ svx₆ svV₆) fun s' ⟨rb, x20, rx, rv, kf, fm, result⟩ => ?_
  have kall := k06.then kf
  refine ⟨?_, fun r hr => ?_, ?_⟩
  · intro r hr
    simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact rb
    · exact x20
    · exact rx 0 (by decide)
    · exact rx 1 (by decide)
    · exact rx 2 (by decide)
    · exact rx 3 (by decide)
    · exact rx 4 (by decide)
    · exact rx 5 (by decide)
    · exact rx 6 (by decide)
    · exact rx 7 (by decide)
    · exact kall.1 _ (by decide)
  · simp only [preservedV, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact rv 0 (by decide)
    · exact rv 1 (by decide)
    · exact rv 2 (by decide)
    · exact rv 3 (by decide)
    · exact rv 4 (by decide)
    · exact rv 5 (by decide)
    · exact rv 6 (by decide)
    · exact rv 7 (by decide)
  · change Spec.X448.bytesAt s'.mem (s₀.gpr .x0) 56 = _
    rw [result, x448_eq]
    apply congrArg Spec.X448.encodeUCoordinate
    rw [e₆, VG.Proof.X448.AArch64.Weak.invEnv_x2, VG.Proof.X448.AArch64.Weak.invEnv_eval, e₅]
    simp (config := {decide := true}) only [opSwap, Function.update_apply, ite_true, ite_false]
    rw [L.x2, L.x3, L.z2, L.z3, cswap_fst, cswap_fst]

end VG.Proof.X448.AArch64.Fast
