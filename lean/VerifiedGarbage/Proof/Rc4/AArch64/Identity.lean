import VerifiedGarbage.Proof.Rc4.AArch64.ApplyStep

namespace VG.Proof.Rc4.AArch64
open VG VG.AArch64 VG.Impl.Rc4.AArch64 VG.Spec.Rc4 VG.Proof.Rc4

def IdentityMem (m : Mem) (p : Addr) (r : Nat) : Mem :=
  fun x => if (x - p).toNat < r then BitVec.ofNat 8 (x - p).toNat else m x

theorem identity_store (m : Mem) (p : Addr) (r : Nat) (hr : r < 256) :
    (IdentityMem m p r).write (p + BitVec.ofNat 64 r) 1 (BitVec.ofNat 8 r) =
      IdentityMem m p (r + 1) := by
  funext x
  rw [write_byte]
  have heq : x = p + BitVec.ofNat 64 r ↔ (x - p).toNat = r := by
    constructor
    · intro h; rw [h, Mem.sub_ofNat_toNat p (by omega)]
    · intro h
      have he : x - p = BitVec.ofNat 64 r := by
        apply BitVec.eq_of_toNat_eq
        rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      have hh := congrArg (· + p) he
      rw [BitVec.sub_add_cancel, BitVec.add_comm] at hh
      exact hh
  simp only [IdentityMem, heq]
  by_cases h : (x - p).toNat = r
  · simp only [h, ite_true, Nat.lt_add_one, Nat.lt_irrefl]
  · by_cases hl : (x - p).toNat < r
    · simp only [h, hl, show (x - p).toNat < r + 1 by omega, ite_true, ite_false]
    · simp only [h, hl, show ¬ (x - p).toNat < r + 1 by omega, ite_false]

def IdentityInv (s₀ : State) (r : Nat) (s : State) : Prop :=
  s.mem = IdentityMem s₀.mem (s₀.gpr .x0) r ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr ∧
    s.gpr .x0 = s₀.gpr .x0 ∧ s.gpr .x1 = s₀.gpr .x1 ∧
    s.gpr .x17 = s₀.gpr .x17 ∧ s.gpr .x9 = s₀.gpr .x9 ∧
    s.gpr .x12 = BitVec.ofNat 64 r

theorem identity_step (s₀ s : State) (r : Nat) (hr : r < 256)
    (hp : InRegions s₀.wr (s₀.gpr .x0) 256) (h : IdentityInv s₀ r s) :
    WP isa (.block identityStep) s fun t => IdentityInv s₀ (r + 1) t ∧
      t.gpr .x11 = BitVec.ofNat 64 (r + 1) - 256#64 := by
  obtain ⟨hm, hrd, hwr, h0, h1, h17, h9, h12⟩ := h
  have hidx : (BitVec.ofNat 8 r).toNat = r := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hr]
  have hw : InRegions s.wr (s₀.gpr .x0 + BitVec.ofNat 64 r) 1 := by
    rw [hwr, ← hidx]
    exact byte_region _ _ _ hp
  rw [hwr] at hw
  have hcast : ((BitVec.ofNat 64 r).setWidth 32).setWidth 8 = BitVec.ofNat 8 r := by bv_omega
  have hadd : BitVec.ofNat 64 r + 1#64 = BitVec.ofNat 64 (r + 1) := by bv_omega
  unfold identityStep
  rrun [State.store, hm, hrd, hwr, h0, h1, h17, h9, h12, hw, hcast, hadd, IdentityInv]
  exact identity_store _ _ _ hr

theorem identity_loop (s₀ s : State) (r : Nat) (hr : r < 256)
    (hp : InRegions s₀.wr (s₀.gpr .x0) 256) (h : IdentityInv s₀ r s) :
    WP isa (.loop (.block identityStep) (.nonzero .x .x11)) s (IdentityInv s₀ 256) := by
  refine WP.loop (M := isa) (fun rem t => ∃ j, j < 256 ∧ rem = 256 - j ∧ IdentityInv s₀ j t)
    ?_ (256 - r) s ⟨r, hr, rfl, h⟩
  intro rem t ⟨j, hj, hrem, ht⟩
  refine WP.mono (identity_step s₀ t j hj hp ht) fun u ⟨hu, hz⟩ => ?_
  by_cases hend : j + 1 = 256
  · left
    refine ⟨?_, hend ▸ hu⟩
    simp [eval, State.read, hz, hend]
  · right
    have hnz : BitVec.ofNat 64 (j + 1) - 256#64 ≠ 0#64 := by bv_omega
    refine ⟨?_, 256 - (j + 1), by omega, j + 1, by omega, rfl, hu⟩
    simp only [eval, State.read, BitVec.setWidth_eq, hz, bne, BitVec.ofNat_eq_ofNat,
      beq_eq_false_iff_ne.mpr hnz]
    rfl

theorem identity_table (m : Mem) (p : Addr) :
    (contextAt (IdentityMem m p 256) p).table =
      Vector.ofFn (fun i : Fin 256 => BitVec.ofNat 8 i.val) := by
  apply Vector.ext
  intro k hk
  simp only [contextAt, Vector.getElem_ofFn, IdentityMem]
  rw [Mem.sub_ofNat_toNat p (by omega), ite_eq_left hk]

end VG.Proof.Rc4.AArch64
