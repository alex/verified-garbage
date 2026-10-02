import VerifiedGarbage.Proof.CmacAes.Arm.Contract
import VerifiedGarbage.Proof.CmacAes.Arm.Words

/-!
# AES-CMAC on ARMv7: `vg_cmac_aes_update`, the blocks before and in the loop

The invariant after `k` blocks (`LInv`): the registers hold the arguments
(`r7` the next block, `r8` the blocks left), only the state, the first 2064
bytes of the scratch buffer and the 8 bytes below the stack pointer have
changed since the registers were saved, and the state is the chaining value
after the first `k` blocks.
-/

namespace VG.Proof.CmacAes.Arm

open VG VG.Arm VG.Impl.CmacAes.Arm
open VG.Proof.MdStream.Arm (Upd Mupd Fupd op2_imm op2_reg wp_mov wp_add wp_subs wp_cmp wp_ldrSp saveMem
  saveList_ok saveMem_frame readW_writeW_save cmp0 ofNat_beq_zero sub_ofNat)

section
variable (s₀ : State)

abbrev W : BitVec 32 := s₀.gpr .r0
abbrev R : Nat := (s₀.gpr .r1).toNat
abbrev St : BitVec 32 := s₀.gpr .r2
abbrev Dp : BitVec 32 := s₀.gpr .r3
abbrev N : Nat := (stackArg s₀ 0).toNat
abbrev S : BitVec 32 := stackArg s₀ 1

abbrev schR : Region := ⟨State.addr (W s₀), 240⟩
abbrev stR : Region := ⟨State.addr (St s₀), 16⟩
abbrev dataR : Region := ⟨State.addr (Dp s₀), 16 * N s₀⟩
abbrev scrR : Region := ⟨State.addr (S s₀), 2176⟩
abbrev argsR : Region := ⟨stackArgAddr s₀ 0, 8⟩
abbrev belowR : Region := ⟨State.addr s₀.sp - BitVec.ofNat 64 8, 8⟩

/-- The cipher. -/
abbrev ciph : Spec.Cmac.Cipher := ciphAt s₀.mem (State.addr (W s₀)) (R s₀)

/-- The message blocks. -/
abbrev blks : List (List Byte) := Spec.Cmac.blocksAt s₀.mem (State.addr (Dp s₀)) 16 (N s₀)

/-- The memory after saving the registers in the scratch buffer. -/
def savedMem : Mem := saveMem s₀.mem (State.addr (S s₀)) s₀.gpr saved

end

/-- The precondition, by name. -/
structure UPre (s₀ : State) : Prop where
  rd : s₀.rd = [schR s₀, dataR s₀, argsR s₀]
  wr : s₀.wr = [stR s₀, scrR s₀]
  sch_st : (schR s₀).Disjoint (stR s₀)
  sch_scr : (schR s₀).Disjoint (scrR s₀)
  data_st : (dataR s₀).Disjoint (stR s₀)
  data_scr : (dataR s₀).Disjoint (scrR s₀)
  st_scr : (stR s₀).Disjoint (scrR s₀)
  st_args : (stR s₀).Disjoint (argsR s₀)
  scr_args : (scrR s₀).Disjoint (argsR s₀)
  b_sch : (belowR s₀).Disjoint (schR s₀)
  b_data : (belowR s₀).Disjoint (dataR s₀)
  b_st : (belowR s₀).Disjoint (stR s₀)
  b_scr : (belowR s₀).Disjoint (scrR s₀)
  sch_fit : (W s₀).toNat + 240 ≤ 2 ^ 32
  st_fit : (St s₀).toNat + 16 ≤ 2 ^ 32
  data_fit : (Dp s₀).toNat + 16 * N s₀ ≤ 2 ^ 32
  scr_fit : (S s₀).toNat + 2176 ≤ 2 ^ 32
  sp8 : 8 ≤ s₀.sp.toNat
  sp_fit : s₀.sp.toNat + 8 ≤ 2 ^ 32
  rounds : R s₀ = 10 ∨ R s₀ = 12 ∨ R s₀ = 14

theorem UPre.of {s₀ : State} (h : updateArm.pre s₀) : UPre s₀ :=
  let ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, t, u⟩ := h
  ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, t, u⟩

/-- The loop invariant, after `k` blocks. -/
structure LInv (s₀ : State) (k : Nat) (s : State) : Prop where
  r4 : s.gpr .r4 = W s₀
  r5 : s.gpr .r5 = s₀.gpr .r1
  r6 : s.gpr .r6 = St s₀
  r7 : s.gpr .r7 = Dp s₀ + BitVec.ofNat 32 (16 * k)
  r8 : s.gpr .r8 = BitVec.ofNat 32 (N s₀ - k)
  r10 : s.gpr .r10 = S s₀
  r11 : s.gpr .r11 = s₀.gpr .r11
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [stR s₀, ⟨State.addr (S s₀), 2064⟩, belowR s₀] (savedMem s₀) s.mem
  state : Spec.Aes.bytesAt s.mem (State.addr (St s₀)) 16 =
    Spec.Cmac.chain (ciph s₀) (Spec.Aes.bytesAt s₀.mem (State.addr (St s₀)) 16) ((blks s₀).take k)

/-! ## Addresses and regions -/

theorem add0 (p : Addr) : p + BitVec.ofNat 64 0 = p := BitVec.add_zero p

section
variable {s₀ : State} (hp : UPre s₀)
include hp

theorem UPre.scrA {d : Nat} (hd : d < 2176) :
    State.addr (S s₀ + BitVec.ofNat 32 d) = State.addr (S s₀) + BitVec.ofNat 64 d :=
  addr_add (by have := hp.scr_fit; have := (S s₀).isLt; omega)

theorem UPre.dataA {k : Nat} (hk : k < N s₀) :
    State.addr (Dp s₀ + BitVec.ofNat 32 (16 * k)) = State.addr (Dp s₀) + BitVec.ofNat 64 (16 * k) :=
  addr_add (by have := hp.data_fit; have := (Dp s₀).isLt; omega)

theorem UPre.dataN {k : Nat} (hk : k < N s₀) :
    (Dp s₀ + BitVec.ofNat 32 (16 * k)).toNat = (Dp s₀).toNat + 16 * k := by
  have := hp.data_fit
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 16 * k) (by omega),
    Nat.mod_eq_of_lt (by omega)]

theorem UPre.scrN {d : Nat} (hd : d < 2176) : (S s₀ + BitVec.ofNat 32 d).toNat = (S s₀).toNat + d := by
  have := hp.scr_fit
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := d) (by omega), Nat.mod_eq_of_lt (by omega)]

omit hp in
theorem UPre.scr_sub {d n : Nat} (h : d + n ≤ 2176) :
    Region.Sub ⟨State.addr (S s₀) + BitVec.ofNat 64 d, n⟩ (scrR s₀) :=
  Offset.sub_base _ h

omit hp in
theorem UPre.data_sub {k : Nat} (hk : k < N s₀) :
    Region.Sub ⟨State.addr (Dp s₀) + BitVec.ofNat 64 (16 * k), 16⟩ (dataR s₀) :=
  Offset.sub_base _ (by omega)

theorem UPre.arg1 : stackArgAddr s₀ 1 = stackArgAddr s₀ 0 + BitVec.ofNat 64 4 := by
  have := hp.sp_fit
  simp only [stackArgAddr]
  rw [addr_add (by omega), addr_add (by omega)]
  simp

theorem UPre.arg_in {k : Nat} (hk : k < 2) : InRegions (s₀.rd ++ s₀.wr) (stackArgAddr s₀ k) 4 := by
  refine ⟨argsR s₀, by simp [hp.rd], ?_⟩
  rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
  · simpa using Offset.contains_base (stackArgAddr s₀ 0) (d := 0) (n := 4) (k := 8) (by decide) (by decide)
  · rw [hp.arg1]; exact Offset.contains_base _ (by decide) (by decide)

omit hp in
theorem UPre.arg_sub : Region.Sub ⟨stackArgAddr s₀ 0, 4⟩ (argsR s₀) := Region.sub_prefix (by decide)

end

/-! ## Saving the registers -/

theorem saved_bound : ∀ p ∈ saved, 2064 ≤ p.2 ∧ p.2 + 4 ≤ 2096 := by decide

theorem saved_ne_r12 : ∀ p ∈ saved, p.1 ≠ .r12 := by decide

theorem saveMem_congr (m : Mem) (B : Addr) {g g' : Reg → BitVec 32} :
    ∀ (l : List (Reg × Nat)), (∀ p ∈ l, g p.1 = g' p.1) → saveMem m B g l = saveMem m B g' l := by
  intro l
  induction l generalizing m with
  | nil => intro _; rfl
  | cons p l ih =>
    intro h
    simp only [saveMem]
    rw [h p (List.mem_cons_self ..)]
    exact ih _ fun q hq => h q (List.mem_cons_of_mem _ hq)

theorem savedMem_frame (s₀ : State) : Frame [⟨State.addr (S s₀), 2096⟩] s₀.mem (savedMem s₀) :=
  saveMem_frame _ _ _ (by decide) saved fun p hp => (saved_bound p hp).2

set_option simprocs false in
/-- Each slot holds the register saved there. -/
theorem savedMem_slot (s₀ : State) {r : Reg} {d : Nat} (h : (r, d) ∈ saved) :
    (savedMem s₀).readW (State.addr (S s₀) + BitVec.ofNat 64 d) 32 = s₀.gpr r := by
  simp only [saved, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ <;>
  simp (disch := decide) only [savedMem, saved, saveMem, Mem.readW_writeW_self32, readW_writeW_save]

/-! ## The prologue -/

theorem prologue_wp {s₀ : State} (hp : UPre s₀) :
    WP isa (.block (save ++ setup)) s₀ fun s => LInv s₀ 0 s ∧ s.z = decide (N s₀ = 0) := by
  have hsc := hp.scr_fit
  rw [show save ++ setup = .ldrSp .r12 4 :: (saved.map (fun p => Instr.str p.1 .r12 p.2) ++ setup) from rfl]
  refine wp_ldrSp (a := stackArgAddr s₀ 1) (by decide) rfl (hp.arg_in (by decide)) fun s₁ u₁ => ?_
  have h12 : s₁.gpr .r12 = S s₀ := u₁.gpr
  refine saveList_ok saved s₁ _ (fun p hp' => ?_) fun s₂ g₂ rd₂ wr₂ sp₂ m₂ => ?_
  · have hb := saved_bound p hp'
    rw [h12, u₁.wr, hp.wr]
    exact ⟨by omega, by omega, ⟨scrR s₀, by simp, Offset.contains_base _ (by omega) (by omega)⟩⟩
  have hm₂ : s₂.mem = savedMem s₀ := by
    rw [m₂, u₁.mem, h12, savedMem]
    exact saveMem_congr _ _ _ fun p hp' => u₁.other _ (saved_ne_r12 p hp')
  have harg : s₂.mem.readW (stackArgAddr s₀ 0) 32 = stackArg s₀ 0 := by
    rw [hm₂]
    exact (savedMem_frame s₀).readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hp.scr_args.symm.sub_left UPre.arg_sub).sub_right (Region.sub_prefix (by decide))) (by decide)
  simp only [setup, mov]
  refine wp_mov (op2_reg _ _) fun s₃ u₃ => wp_mov (op2_reg _ _) fun s₄ u₄ => wp_mov (op2_reg _ _) fun s₅ u₅ =>
    wp_mov (op2_reg _ _) fun s₆ u₆ => ?_
  refine wp_ldrSp (a := stackArgAddr s₀ 0) (by decide) (by rw [u₆.sp, u₅.sp, u₄.sp, u₃.sp, sp₂, u₁.sp]; rfl)
    (by rw [u₆.rd, u₆.wr, u₅.rd, u₅.wr, u₄.rd, u₄.wr, u₃.rd, u₃.wr, rd₂, wr₂, u₁.rd, u₁.wr]
        exact hp.arg_in (by decide)) fun s₇ u₇ => ?_
  refine wp_mov (op2_reg _ _) fun s₈ u₈ => wp_cmp (op2_imm (by decide)) fun s₉ f₉ z₉ => WP.block_nil ?_
  have r8 : s₉.gpr .r8 = stackArg s₀ 0 := by
    rw [f₉.gpr, u₈.other _ (by decide), u₇.gpr, u₆.mem, u₅.mem, u₄.mem, u₃.mem, harg]
  have mm : s₉.mem = savedMem s₀ := by
    rw [f₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, hm₂]
  have a0 : stackArg s₀ 0 = BitVec.ofNat 32 (N s₀) := by simp [N]
  have stS : Spec.Aes.bytesAt (savedMem s₀) (State.addr (St s₀)) 16 =
      Spec.Aes.bytesAt s₀.mem (State.addr (St s₀)) 16 :=
    Proof.Cmac.bytesAt_frame16 (savedMem_frame s₀) fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.st_scr.sub_right (Region.sub_prefix (by decide))
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp (disch := decide) only [f₉.gpr, u₈.other, u₇.other, u₆.other, u₅.other, u₄.other, u₃.gpr, g₂, u₁.other]
  · simp (disch := decide) only [f₉.gpr, u₈.other, u₇.other, u₆.other, u₅.other, u₄.gpr, u₃.other, g₂, u₁.other]
  · simp (disch := decide) only [f₉.gpr, u₈.other, u₇.other, u₆.other, u₅.gpr, u₄.other, u₃.other, g₂, u₁.other]
  · simp (disch := decide) only [f₉.gpr, u₈.other, u₇.other, u₆.gpr, u₅.other, u₄.other, u₃.other, g₂, u₁.other]
    exact (BitVec.add_zero _).symm
  · rw [r8, a0]; rfl
  · simp (disch := decide) only [f₉.gpr, u₈.gpr, u₇.other, u₆.other, u₅.other, u₄.other, u₃.other, g₂, h12]
  · simp (disch := decide) only [f₉.gpr, u₈.other, u₇.other, u₆.other, u₅.other, u₄.other, u₃.other, g₂,
      u₁.other]
  · rw [f₉.sp, u₈.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, sp₂, u₁.sp]
  · rw [f₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, rd₂, u₁.rd]
  · rw [f₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, wr₂, u₁.wr]
  · rw [mm]; exact Frame.refl _ _
  · rw [mm, stS]; rfl
  · rw [z₉, show s₈.gpr .r8 = s₉.gpr .r8 from (congrFun f₉.gpr _).symm, r8, a0]
    exact cmp0 (stackArg s₀ 0).isLt

end VG.Proof.CmacAes.Arm
