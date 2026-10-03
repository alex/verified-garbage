import VerifiedGarbage.Proof.CmacAes.X86.Save

/-!
# AES-CMAC on x86: `vg_cmac_aes_update`, the blocks before and in the loop

The invariant after `k` blocks (`LInv`): `esi` points at the next block, `esp`
is unchanged, only the state, the first 2064 bytes of the scratch buffer and
the 28 bytes below `esp` have changed since the registers were saved, and the
state is the chaining value after the first `k` blocks. Everything else is
reloaded from the stack arguments, which nothing writes.
-/

namespace VG.Proof.CmacAes.X86

open VG VG.X86 VG.Impl.CmacAes.X86
open VG.Proof.MdStream.X86 (Upd Mupd Fupd wp_mov wp_movi wp_addi wp_add wp_cmp wp_test)

section
variable (s₀ : State)

abbrev E : BitVec 32 := s₀.gpr .esp
abbrev W : BitVec 32 := arg s₀ 0
abbrev R : Nat := (arg s₀ 1).toNat
abbrev St : BitVec 32 := arg s₀ 2
abbrev Dp : BitVec 32 := arg s₀ 3
abbrev N : Nat := (arg s₀ 4).toNat
abbrev S : BitVec 32 := arg s₀ 5

abbrev schR : Region := ⟨(W s₀).setWidth 64, 240⟩
abbrev stR : Region := ⟨(St s₀).setWidth 64, 16⟩
abbrev dataR : Region := ⟨(Dp s₀).setWidth 64, 16 * N s₀⟩
abbrev scrR : Region := ⟨(S s₀).setWidth 64, 2176⟩
abbrev argsR : Region := ⟨argAddr s₀ 0, 24⟩
abbrev retR : Region := ⟨(E s₀).setWidth 64, 4⟩
abbrev stkR : Region := ⟨(E s₀).setWidth 64 - BitVec.ofNat 64 28, 28⟩

/-- The cipher. -/
abbrev ciph : Spec.Cmac.Cipher := ciphAt s₀.mem ((W s₀).setWidth 64) (R s₀)

/-- The message blocks. -/
abbrev blks : List (List Byte) := Spec.Cmac.blocksAt s₀.mem ((Dp s₀).setWidth 64) 16 (N s₀)

/-- The memory after saving the registers in the scratch buffer. -/
def savedMem : Mem := Spill.saveMem s₀.mem ((S s₀).setWidth 64 + BitVec.ofNat 64 ·) s₀.gpr saved

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
  args_st : (argsR s₀).Disjoint (stR s₀)
  args_scr : (argsR s₀).Disjoint (scrR s₀)
  ret_st : (retR s₀).Disjoint (stR s₀)
  ret_scr : (retR s₀).Disjoint (scrR s₀)
  b_sch : (stkR s₀).Disjoint (schR s₀)
  b_data : (stkR s₀).Disjoint (dataR s₀)
  b_st : (stkR s₀).Disjoint (stR s₀)
  b_scr : (stkR s₀).Disjoint (scrR s₀)
  sch_fit : (W s₀).toNat + 240 ≤ 2 ^ 32
  st_fit : (St s₀).toNat + 16 ≤ 2 ^ 32
  data_fit : (Dp s₀).toNat + 16 * N s₀ ≤ 2 ^ 32
  scr_fit : (S s₀).toNat + 2176 ≤ 2 ^ 32
  esp28 : 28 ≤ (E s₀).toNat
  esp_fit : (E s₀).toNat + 28 ≤ 2 ^ 32
  rounds : R s₀ = 10 ∨ R s₀ = 12 ∨ R s₀ = 14

theorem UPre.of {s₀ : State} (h : updateX86.pre s₀) : UPre s₀ :=
  let ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, t, u, v, w⟩ := h
  ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, t, u, v, w⟩

/-- The loop invariant, after `k` blocks. -/
structure LInv (s₀ : State) (k : Nat) (s : State) : Prop where
  esi : s.gpr .esi = Dp s₀ + BitVec.ofNat 32 (16 * k)
  esp : s.gpr .esp = E s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [stR s₀, ⟨(S s₀).setWidth 64, 2064⟩, stkR s₀] (savedMem s₀) s.mem
  state : Spec.Aes.bytesAt s.mem ((St s₀).setWidth 64) 16 =
    Spec.Cmac.chain (ciph s₀) (Spec.Aes.bytesAt s₀.mem ((St s₀).setWidth 64) 16) ((blks s₀).take k)

/-! ## Addresses and regions -/

theorem add0 (p : Addr) : p + BitVec.ofNat 64 0 = p := BitVec.add_zero p

theorem add0' (p : BitVec 32) : p + BitVec.ofNat 32 0 = p := BitVec.add_zero p

/-- The regions the function writes, with the stack below it. -/
abbrev Big (s₀ : State) : List Region := [stR s₀, scrR s₀, stkR s₀]

section
variable {s₀ : State} (hp : UPre s₀)
include hp

theorem UPre.below_eq : below (E s₀) 28 = stkR s₀ := by
  simp only [below]; rw [Taint.sub_setWidth hp.esp28]

theorem UPre.argA {i : Nat} (hi : i < 6) : argAddr s₀ i = argAddr s₀ 0 + BitVec.ofNat 64 (4 * i) := by
  have : (s₀.gpr .esp).toNat + 28 ≤ 2 ^ 32 := hp.esp_fit
  simp only [argAddr]
  rw [show (s₀.gpr .esp + BitVec.ofNat 32 (4 + 4 * i)).setWidth 64 = addr (s₀.gpr .esp) (4 + 4 * i) from rfl,
    show (s₀.gpr .esp + BitVec.ofNat 32 (4 + 4 * 0)).setWidth 64 = addr (s₀.gpr .esp) (4 + 4 * 0) from rfl,
    addr_eq (by omega), addr_eq (by omega), Offset.add_add]

theorem UPre.arg_sub {i : Nat} (hi : i < 6) : Region.Sub ⟨argAddr s₀ i, 4⟩ (argsR s₀) := by
  rw [hp.argA hi]; exact Offset.sub_base _ (by omega)

theorem UPre.arg_in {i : Nat} (hi : i < 6) : InRegions (s₀.rd ++ s₀.wr) (argAddr s₀ i) 4 := by
  refine ⟨argsR s₀, by simp [hp.rd], ?_⟩
  rw [hp.argA hi]; exact Offset.contains_base _ (by omega) (by omega)

theorem UPre.args_stk : (argsR s₀).Disjoint (stkR s₀) := by
  have : (s₀.gpr .esp).toNat + 28 ≤ 2 ^ 32 := hp.esp_fit
  have e : argAddr s₀ 0 = (E s₀).setWidth 64 + BitVec.ofNat 64 4 := addr_eq (by omega)
  show Region.Disjoint ⟨argAddr s₀ 0, 24⟩ _
  rw [e]; exact (Offset.disjoint_below_above _ (by decide)).symm

/-- The stack arguments are unchanged where only `Big` changes. -/
theorem UPre.arg_keep {m : Mem} (hf : Frame (Big s₀) s₀.mem m) {i : Nat} (hi : i < 6) :
    m.readW (argAddr s₀ i) 32 = arg s₀ i :=
  hf.readW (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.args_st.sub_left (hp.arg_sub hi)
    · exact hp.args_scr.sub_left (hp.arg_sub hi)
    · exact hp.args_stk.sub_left (hp.arg_sub hi)) (by decide)

theorem UPre.dataA {k : Nat} (hk : k < N s₀) :
    addr (Dp s₀) (16 * k) = (Dp s₀).setWidth 64 + BitVec.ofNat 64 (16 * k) :=
  addr_eq (by have := hp.data_fit; omega)

theorem UPre.dataN {k : Nat} (hk : k < N s₀) :
    (Dp s₀ + BitVec.ofNat 32 (16 * k)).toNat = (Dp s₀).toNat + 16 * k := by
  have := hp.data_fit
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 16 * k) (by omega),
    Nat.mod_eq_of_lt (by omega)]

theorem UPre.scrN {d : Nat} (hd : d < 2176) : (S s₀ + BitVec.ofNat 32 d).toNat = (S s₀).toNat + d := by
  have := hp.scr_fit
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := d) (by omega), Nat.mod_eq_of_lt (by omega)]

theorem UPre.scrA {d : Nat} (hd : d < 2176) :
    (S s₀ + BitVec.ofNat 32 d).setWidth 64 = (S s₀).setWidth 64 + BitVec.ofNat 64 d :=
  addr_eq (by have := hp.scr_fit; omega)

end

theorem UPre.scr_sub {s₀ : State} {d n : Nat} (h : d + n ≤ 2176) :
    Region.Sub ⟨(S s₀).setWidth 64 + BitVec.ofNat 64 d, n⟩ (scrR s₀) :=
  Offset.sub_base _ h

theorem UPre.data_sub {s₀ : State} {k : Nat} (hk : k < N s₀) :
    Region.Sub ⟨(Dp s₀).setWidth 64 + BitVec.ofNat 64 (16 * k), 16⟩ (dataR s₀) :=
  Offset.sub_base _ (by omega)

theorem savedMem_frame (s₀ : State) : Frame [scrR s₀] s₀.mem (savedMem s₀) :=
  Spill.saveMem_frame List.mem_cons_self _ _ _ _ fun p hp =>
    have := saved_bound p hp; Offset.contains_base _ (by omega) (by omega)

theorem savedMem_slot (s₀ : State) {r : Reg} {d : Nat} (h : (r, d) ∈ saved) :
    (savedMem s₀).readW ((S s₀).setWidth 64 + BitVec.ofNat 64 d) 32 = s₀.gpr r :=
  saveMem_slot _ _ _ h

/-- `savedMem` changes only `Big`. -/
theorem savedMem_big (s₀ : State) : Frame (Big s₀) s₀.mem (savedMem s₀) :=
  (savedMem_frame s₀).mono (by simp)

/-! ## The prologue -/

theorem setup_eq : setup = .mov .eax (argOp 5) :: (saved.map (fun p => Instr.store (at_ .eax p.2) p.1) ++
    ([.mov .esi (argOp 3), .mov .eax (argOp 4), .alu .test .eax (.reg .eax)] : List Instr)) := rfl

theorem ofNat_and_self_beq {k : Nat} (h : k < 2 ^ 32) : (BitVec.ofNat 32 k &&& BitVec.ofNat 32 k == 0) = decide (k = 0) := by
  rw [BitVec.and_self]; exact MdStream.X86.ofNat_beq_zero h

theorem arg_ofNat (s₀ : State) (i : Nat) : arg s₀ i = BitVec.ofNat 32 (arg s₀ i).toNat := by simp

theorem prologue_wp {s₀ : State} (hp : UPre s₀) :
    WP isa (.block setup) s₀ fun s => LInv s₀ 0 s ∧ s.zf = some (decide (N s₀ = 0)) := by
  have hsc := hp.scr_fit
  rw [setup_eq]
  refine wp_arg (s₀ := s₀) rfl (hp.arg_in (by decide)) rfl fun s₁ u₁ => ?_
  have h₁ : s₁.gpr .eax = S s₀ := u₁.gpr
  refine Spill.save_ofNat_ok saved saved_fits (by rw [h₁]; omega) (fun p hp' => ?_) fun s₂ u₂ => ?_
  · have hb := saved_bound p hp'
    rw [h₁, u₁.wr, hp.wr]
    exact ⟨scrR s₀, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  have hm₂ : s₂.mem = savedMem s₀ := by
    rw [u₂.mem, u₁.mem, h₁, savedMem]
    exact Spill.saveMem_congr _ _ (fun _ _ => rfl) fun p hp' => u₁.other _ (saved_ne_eax p hp')
  have esp₂ : s₂.gpr .esp = s₀.gpr .esp := by rw [u₂.gpr, u₁.other _ (by decide)]
  have rw₂ : s₂.rd ++ s₂.wr = s₀.rd ++ s₀.wr := by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]
  refine wp_arg (s₀ := s₀) esp₂ (by rw [rw₂]; exact hp.arg_in (by decide))
    (by rw [hm₂]; exact hp.arg_keep (savedMem_big s₀) (by decide)) fun s₃ u₃ => ?_
  refine wp_arg (s₀ := s₀) (by rw [u₃.other _ (by decide), esp₂])
    (by rw [u₃.rd, u₃.wr, rw₂]; exact hp.arg_in (by decide))
    (by rw [u₃.mem, hm₂]; exact hp.arg_keep (savedMem_big s₀) (by decide)) fun s₄ u₄ => ?_
  refine wp_test fun s₅ f₅ z₅ => WP.block_nil ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [f₅.gpr, u₄.other _ (by decide), u₃.gpr, Nat.mul_zero, add0']
  · rw [f₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), esp₂]
  · rw [f₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [f₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  · rw [f₅.mem, u₄.mem, u₃.mem, hm₂]; exact Frame.refl _ _
  · rw [f₅.mem, u₄.mem, u₃.mem, hm₂, Proof.Cmac.bytesAt_frame16 (savedMem_frame s₀) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.st_scr)]
    rfl
  · rw [z₅, u₄.gpr, arg_ofNat s₀ 4, ofNat_and_self_beq (arg s₀ 4).isLt]

end VG.Proof.CmacAes.X86
