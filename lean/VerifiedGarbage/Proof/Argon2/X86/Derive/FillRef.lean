import VerifiedGarbage.Proof.Argon2.X86.Derive.FillCache
import VerifiedGarbage.Proof.Argon2.Reference

/-!
# Argon2 on x86 (32-bit): the reference block's lane, start and base

`RS`: the filling state with J₁ and J₂ in the locals. `refLane_ok`: the
reference lane (RFC 9106 §3.4.2); `refStart_ok`: where the window of
eligible blocks starts; `countBase_ok`: the blocks before the current
segment that a reference may use.
-/

namespace VG.Proof.Argon2.X86.Derive

open VG VG.X86
open VG.X86.Wp (Upd Mupd Fupd wp_movi wp_mov wp_add wp_addi wp_subi wp_addm wp_cmpi wp_ldm wp_stm wp_andi
  wp_sbb_self wp_and wp_xor)
open VG.Spec.Argon2 (Block blockAt zeroBlock FillState)
open VG.Impl.Argon2.X86.Derive (sliceOff segLenOff indexOff laneOff laneLenOff argOff passOff counterOff
  j1Off j2Off refLaneOff startOff countOff tmpOff curOff)

/-- The filling state, with J₁ and J₂ in the locals. -/
structure RS (s₀ : State) (pass slice lane index ctr : Nat) (st : FillState) (J1 J2 : BitVec 32) (s : State) :
    Prop where
  fs : FS s₀ pass slice lane index ctr st s
  j1 : lw s₀ s j1Off = J1
  j2 : lw s₀ s j2Off = J2

theorem RS.of_keep {s₀ s t : State} {pass slice lane index ctr : Nat} {st : FillState} {J1 J2 : BitVec 32}
    (h : RS s₀ pass slice lane index ctr st J1 J2 s) (k : Divide.Keep s t) : RS s₀ pass slice lane index ctr st J1 J2 t :=
  ⟨h.fs.of_keep k, by rw [lw_mem k.mem]; exact h.j1, by rw [lw_mem k.mem]; exact h.j2⟩

/-- The reference lane: J₂ mod the lane count, but the current lane in the first slice of the first pass. -/
def refLaneV (lanes pass slice lane j2 : Nat) : Nat := if pass = 0 ∧ slice = 0 then lane else j2 % lanes

/-- Where the window starts. -/
def startV (segLen laneLen pass slice : Nat) : Nat :=
  if pass = 0 then 0 else (slice + 1) * segLen % laneLen

/-- The blocks before the current segment that a reference may use. -/
def baseV (segLen laneLen pass slice : Nat) : Nat := if pass = 0 then slice * segLen else laneLen - segLen

theorem or_zero {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    (BitVec.ofNat 32 a ||| BitVec.ofNat 32 b == 0) = decide (a = 0 ∧ b = 0) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
  constructor
  · intro e
    have := congrArg BitVec.toNat e
    rw [BitVec.toNat_or, Wp.toNat_ofNat_lt ha, Wp.toNat_ofNat_lt hb] at this
    simpa using this
  · rintro ⟨rfl, rfl⟩; rfl

section
variable {s₀ : State} (hp : DPre s₀)
include hp

theorem RS.store {s t : State} {pass slice lane index ctr : Nat} {st : FillState} {J1 J2 : BitVec 32}
    (h : RS s₀ pass slice lane index ctr st J1 J2 s) (it : Inv s₀ t) {d : Nat} (hd : d + 4 ≤ 144) (ha : d % 4 = 0)
    (hd' : d ∉ fsOffs) (h1 : d ≠ j1Off) (h2 : d ≠ j2Off) {v : BitVec 32}
    (hm : t.mem = s.mem.writeW (addr (E s₀) d) v) : RS s₀ pass slice lane index ctr st J1 J2 t := by
  refine ⟨h.fs.store hp it hd ha hd' hm, ?_, ?_⟩
  · show t.mem.readW _ 32 = _
    rw [hm, lw_store hp (by omega) (by decide) (by simp [j1Off] at h1 ⊢; omega)]; exact h.j1
  · show t.mem.readW _ 32 = _
    rw [hm, lw_store hp (by omega) (by decide) (by simp [j2Off] at h2 ⊢; omega)]; exact h.j2

/-- The block of `refLane`: J₂ mod lanes, to the locals, and ZF in the first
slice of the first pass. -/
theorem refLaneBlk_ok {s : State} {pass slice lane index ctr : Nat} {st : FillState} {J1 J2 : BitVec 32}
    (h : RS s₀ pass slice lane index ctr st J1 J2 s) (hpass : pass < 2 ^ 32) (hs : slice < 4) :
    WP isa (.block (.mov .ecx (Impl.Argon2.X86.Derive.fr j2Off) :: Impl.Argon2.X86.Divide.code (argOff 7) ++
      [Impl.Argon2.X86.Derive.st refLaneOff .eax, .mov .eax (Impl.Argon2.X86.Derive.fr passOff),
        .alu .or .eax (Impl.Argon2.X86.Derive.fr sliceOff)])) s fun t =>
      RS s₀ pass slice lane index ctr st J1 J2 t ∧ t.zf = some (decide (pass = 0 ∧ slice = 0)) ∧
      lw s₀ t refLaneOff = BitVec.ofNat 32 (J2.toNat % lanesN s₀) := by
  have hlt := hp.lanes_lt
  have hl1 := hp.lanes_pos
  have e7 : lanesN s₀ = (arg s₀ 7).toNat := rfl
  simp only [List.cons_append]
  refine wp_ldloc hp h.fs.inv (d := j2Off) (by decide) fun s₁ u₁ => ?_
  have h₁ := h.of_keep (Divide.Keep.of_upd u₁ (by simp))
  refine Divide.code_ok (D := arg s₀ 7) (by omega) (by omega) h₁.fs.inv.ebp (h₁.fs.inv.arg_in hp (by decide))
    (h₁.fs.inv.arg hp (by decide)) fun s₂ _ r₂ k₂ => ?_
  have h₂ := h₁.of_keep k₂
  refine wp_stloc hp h₂.fs.inv (d := refLaneOff) (by decide) fun s₃ i₃ v₃ _ g₃ m₃ => ?_
  have h₃ := h₂.store hp i₃ (d := refLaneOff) (by decide) (by decide) (by decide) (by decide) (by decide) m₃
  refine wp_ldloc hp h₃.fs.inv (d := passOff) (by decide) fun s₄ u₄ => ?_
  have h₄ := h₃.of_keep (Divide.Keep.of_upd u₄ (by simp))
  refine wp_orm h₄.fs.inv.ebp (loc_in' hp h₄.fs.inv (d := sliceOff) (by decide)) fun s₅ u₅ z₅ => WP.block_nil ?_
  have h₅ := h₄.of_keep (Divide.Keep.of_upd u₅ (by simp))
  have r : s₂.gpr .eax = BitVec.ofNat 32 (J2.toNat % lanesN s₀) := BitVec.eq_of_toNat_eq (by
    rw [r₂, u₁.gpr, h.j2, Wp.toNat_ofNat_lt (by have := J2.isLt; have := Nat.mod_le J2.toNat (lanesN s₀); omega)])
  refine ⟨h₅, ?_, by rw [lw_mem u₅.mem, lw_mem u₄.mem, v₃, r]⟩
  rw [z₅, u₄.gpr, show s₄.mem.readW (addr (E s₀) sliceOff) 32 = lw s₀ s₄ sliceOff from rfl, h₄.fs.pos.slice,
    h₃.fs.pos.pass, or_zero hpass (by omega)]

/-- `refLane`: the reference lane, to the locals. -/
theorem refLane_ok {s : State} {pass slice lane index ctr : Nat} {st : FillState} {J1 J2 : BitVec 32}
    (h : RS s₀ pass slice lane index ctr st J1 J2 s) (hpass : pass < 2 ^ 32) (hs : slice < 4) :
    WP isa Impl.Argon2.X86.Derive.refLane s fun t => RS s₀ pass slice lane index ctr st J1 J2 t ∧
      lw s₀ t refLaneOff = BitVec.ofNat 32 (refLaneV (lanesN s₀) pass slice lane J2.toNat) := by
  unfold Impl.Argon2.X86.Derive.refLane
  refine WP.seq ((refLaneBlk_ok hp h hpass hs).mono fun s₅ ⟨h₅, z₅, e₃⟩ => ?_)
  refine WP.ite (decide (pass = 0 ∧ slice = 0)) z₅ (fun hb => ?_) fun hb => ?_
  · have hb' : pass = 0 ∧ slice = 0 := of_decide_eq_true hb
    refine wp_ldloc hp h₅.fs.inv (d := laneOff) (by decide) fun s₆ u₆ => ?_
    have h₆ := h₅.of_keep (Divide.Keep.of_upd u₆ (by simp))
    refine wp_stloc hp h₆.fs.inv (d := refLaneOff) (by decide) fun t it vt _ _ mt => WP.block_nil ⟨?_, ?_⟩
    · exact h₆.store hp it (d := refLaneOff) (by decide) (by decide) (by decide) (by decide) (by decide) mt
    · rw [vt, u₆.gpr, h₅.fs.pos.lane, refLaneV, ite_eq_left hb']
  · have hb' : ¬(pass = 0 ∧ slice = 0) := of_decide_eq_false hb
    refine WP.block_nil ⟨h₅, ?_⟩
    rw [e₃, refLaneV, ite_eq_right hb']

end


section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- `refStart`: where the window starts, to the locals. -/
theorem refStart_ok {s : State} {pass slice lane index ctr : Nat} {st : FillState} {J1 J2 : BitVec 32}
    (h : RS s₀ pass slice lane index ctr st J1 J2 s) (hpass : pass < 2 ^ 32) (hs : slice < 4) :
    WP isa Impl.Argon2.X86.Derive.refStart s fun t => RS s₀ pass slice lane index ctr st J1 J2 t ∧
      lw s₀ t refLaneOff = lw s₀ s refLaneOff ∧
      lw s₀ t startOff = BitVec.ofNat 32 (startV (prm s₀).segmentLen (prm s₀).laneLen pass slice) := by
  have sl := segLen_lt hp
  have ll := hp.laneLen_eq
  have s2 := hp.segLen_two
  unfold Impl.Argon2.X86.Derive.refStart
  refine WP.seq (wp_movi fun s₁ u₁ => ?_)
  have h₁ := h.of_keep (Divide.Keep.of_upd u₁ (by simp))
  refine wp_stloc hp h₁.fs.inv (d := startOff) (by decide) fun s₂ i₂ v₂ o₂ _ m₂ => ?_
  have h₂ := h₁.store hp i₂ (d := startOff) (by decide) (by decide) (by decide) (by decide) (by decide) m₂
  refine wp_ldloc hp h₂.fs.inv (d := passOff) (by decide) fun s₃ u₃ => wp_cmpi fun s₄ f₄ _ z₄ => WP.block_nil ?_
  have h₄ := (h₂.of_keep (Divide.Keep.of_upd u₃ (by simp))).of_keep (Divide.Keep.of_fupd f₄)
  have m₄ : s₄.mem = s₂.mem := by rw [f₄.mem, u₃.mem]
  have r₂ : lw s₀ s₂ refLaneOff = lw s₀ s refLaneOff := by
    rw [o₂ _ (by decide) (by decide), lw_mem u₁.mem]
  have z : ∀ y : BitVec 32, y - 0 = y := fun y => by simp
  refine WP.ite (decide (pass = 0)) (by
    show s₄.zf = _
    rw [z₄, u₃.gpr, h₂.fs.pos.pass, z, Wp.ofNat_beq_zero hpass]) (fun hb => ?_) fun hb => ?_
  · refine WP.block_nil ⟨h₄, by rw [lw_mem m₄, r₂], ?_⟩
    rw [lw_mem m₄, v₂, u₁.gpr, startV, ite_eq_left (of_decide_eq_true hb)]; rfl
  · have hp0 : pass ≠ 0 := of_decide_eq_false hb
    refine WP.seq (wp_ldloc hp h₄.fs.inv (d := sliceOff) (by decide) fun s₅ u₅ => wp_cmpi fun s₆ f₆ _ z₆ =>
      WP.block_nil ?_)
    have h₆ := (h₄.of_keep (Divide.Keep.of_upd u₅ (by simp))).of_keep (Divide.Keep.of_fupd f₆)
    have m₆ : s₆.mem = s₂.mem := by rw [f₆.mem, u₅.mem, m₄]
    refine WP.ite (decide (slice = 3)) (by
      show s₆.zf = _
      rw [z₆, u₅.gpr, h₄.fs.pos.slice, show (3 : BitVec 32) = BitVec.ofNat 32 3 from rfl,
        Wp.sub_beq (by omega) (by decide)]) (fun hb' => ?_) fun hb' => ?_
    · refine WP.block_nil ⟨h₆, by rw [lw_mem m₆, r₂], ?_⟩
      rw [lw_mem m₆, v₂, u₁.gpr, startV, ite_eq_right hp0, of_decide_eq_true hb', ll, Nat.mod_self]; rfl
    · have hs3 : slice ≠ 3 := of_decide_eq_false hb'
      refine wp_ldloc hp h₆.fs.inv (d := sliceOff) (by decide) fun s₇ u₇ => wp_addi fun s₈ u₈ =>
        wp_ldloc hp ((h₆.of_keep (Divide.Keep.of_upd u₇ (by simp))).of_keep (Divide.Keep.of_upd u₈ (by simp))).fs.inv
          (d := segLenOff) (by decide) fun s₉ u₉ => wp_mul fun s₁₀ a₁₀ _ k₁₀ _ => ?_
      have h₁₀ := ((((h₆.of_keep (Divide.Keep.of_upd u₇ (by simp))).of_keep (Divide.Keep.of_upd u₈ (by simp))).of_keep
        (Divide.Keep.of_upd u₉ (by simp))).of_keep k₁₀)
      have m₁₀ : s₁₀.mem = s₂.mem := by rw [k₁₀.mem, u₉.mem, u₈.mem, u₇.mem, m₆]
      refine wp_stloc hp h₁₀.fs.inv (d := startOff) (by decide) fun t it vt ot _ mt => WP.block_nil ⟨?_, ?_, ?_⟩
      · exact h₁₀.store hp it (d := startOff) (by decide) (by decide) (by decide) (by decide) (by decide) mt
      · rw [ot _ (by decide) (by decide), lw_mem m₁₀, r₂]
      · have : (slice + 1) * (prm s₀).segmentLen < (prm s₀).laneLen := by
          rw [ll]; exact Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
        rw [vt, a₁₀, u₉.other _ (by decide), u₈.gpr, u₇.gpr, u₉.gpr, lw_mem u₈.mem, lw_mem u₇.mem,
          h₆.fs.pr.segLen, lw_mem (show s₆.mem = s₂.mem from m₆), h₂.fs.pos.slice,
          show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, BitVec.ofNat_add_ofNat, Wp.toNat_ofNat_lt (by omega),
          Wp.toNat_ofNat_lt (by omega), startV, ite_eq_right hp0, Nat.mod_eq_of_lt this]

end

section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- `countBase`: `eax :=` the blocks before the current segment that a reference may use. -/
theorem countBase_ok {s : State} {pass slice lane index ctr : Nat} {st : FillState} {J1 J2 : BitVec 32}
    (h : RS s₀ pass slice lane index ctr st J1 J2 s) (hpass : pass < 2 ^ 32) (hs : slice < 4) :
    WP isa Impl.Argon2.X86.Derive.countBase s fun t => Divide.Keep s t ∧
      t.gpr .eax = BitVec.ofNat 32 (baseV (prm s₀).segmentLen (prm s₀).laneLen pass slice) := by
  have sl := segLen_lt hp
  have ll := hp.laneLen_eq
  unfold Impl.Argon2.X86.Derive.countBase
  refine WP.seq (wp_ldloc hp h.fs.inv (d := passOff) (by decide) fun s₁ u₁ => wp_cmpi fun s₂ f₂ _ z₂ =>
    WP.block_nil ?_)
  have k₂ := (Divide.Keep.of_upd u₁ (by simp)).trans (Divide.Keep.of_fupd f₂)
  have h₂ := h.of_keep k₂
  have z : ∀ y : BitVec 32, y - 0 = y := fun y => by simp
  refine WP.ite (decide (pass = 0)) (by
    show s₂.zf = _
    rw [z₂, u₁.gpr, h.fs.pos.pass, z, Wp.ofNat_beq_zero hpass]) (fun hb => ?_) fun hb => ?_
  · refine wp_ldloc hp h₂.fs.inv (d := sliceOff) (by decide) fun s₃ u₃ =>
      wp_ldloc hp (h₂.of_keep (Divide.Keep.of_upd u₃ (by simp))).fs.inv (d := segLenOff) (by decide) fun s₄ u₄ =>
      wp_mul fun t a _ k _ => WP.block_nil ⟨k₂.trans ((Divide.Keep.of_upd u₃ (by simp)).trans
        ((Divide.Keep.of_upd u₄ (by simp)).trans k)), ?_⟩
    rw [a, u₄.other _ (by decide), u₃.gpr, u₄.gpr, lw_mem u₃.mem, h₂.fs.pos.slice, h₂.fs.pr.segLen,
      Wp.toNat_ofNat_lt (by omega), Wp.toNat_ofNat_lt (by omega), baseV, ite_eq_left (of_decide_eq_true hb)]
  · refine wp_ldloc hp h₂.fs.inv (d := laneLenOff) (by decide) fun s₃ u₃ =>
      Divide.wp_subm (h₂.of_keep (Divide.Keep.of_upd u₃ (by simp))).fs.inv.ebp
        (loc_in' hp (h₂.of_keep (Divide.Keep.of_upd u₃ (by simp))).fs.inv (d := segLenOff) (by decide))
        fun t u _ => WP.block_nil ⟨k₂.trans ((Divide.Keep.of_upd u₃ (by simp)).trans
          (Divide.Keep.of_upd u (by simp))), ?_⟩
    rw [u.gpr, u₃.gpr, show s₃.mem.readW (addr (E s₀) segLenOff) 32 = lw s₀ s₃ segLenOff from rfl,
      lw_mem u₃.mem, h₂.fs.pr.laneLen, h₂.fs.pr.segLen, Wp.sub_ofNat (by omega), baseV,
      ite_eq_right (of_decide_eq_false hb)]

end
end VG.Proof.Argon2.X86.Derive
