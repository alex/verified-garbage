import VerifiedGarbage.Proof.Aes.X86.Group
import VerifiedGarbage.Proof.Aes.X86.Ctr32CT
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Gcm.Contract
import VerifiedGarbage.Proof.Gcm.Spec

/-!
# AES counter mode on x86 (32-bit): the whole function

Untrusted: everything here is checked by Lean.

The prologue saves the callee-saved registers in the scratch buffer, copies
the counter block's words to it and writes back the final counter; the key
loop (`Keys.lean`) and the group loop (`Group.lean`) do the rest, and the
epilogue restores the registers. Constant time is `Ctr32CT.lean`.
-/

namespace VG.Proof.Aes.X86

open VG VG.X86 VG.X86.Straight VG.Bitslice VG.Impl.Aes.X86 VG.Proof.Aes VG.Proof.Aes.Ct32
open VG.X86.Wp (Upd Mupd Fupd wp_mov wp_movi wp_addi wp_add wp_addm wp_sub wp_subi wp_cmp wp_cmpi wp_test
  wp_bswap wp_ldm wp_xorm wp_stm sub_beq sub_ofNat toNat_ofNat_lt ofNat_pred ofNat_beq_zero)

theorem arg_eq (s : State) (i : Nat) : arg s i = s.mem.readW (addr (s.gpr .esp) (4 + 4 * i)) 32 := rfl

/-! ## The prologue -/

/-- After the prologue. -/
structure P1 (s₀ s : State) : Prop where
  esp : s.gpr .esp = s₀.gpr .esp
  edi : s.gpr .edi = scrP s₀
  esi : s.gpr .esi = arg s₀ 1
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [⟨addr (scrP s₀) 256, 32⟩, ⟨addr (ctrP s₀) 12, 4⟩] s₀.mem s.mem
  saved : ∀ p ∈ savedRegs, s.mem.readW (addr (scrP s₀) p.2) 32 = s₀.gpr p.1
  cw : ∀ v < 3, cw s.mem (scrP s₀) v = s₀.mem.readW (addr (ctrP s₀) (4 * v)) 32
  cnum : cnum s.mem (scrP s₀) = bswap (s₀.mem.readW (addr (ctrP s₀) 12) 32)
  ctr : s.mem.readW (addr (ctrP s₀) 12) 32 =
    bswap (bswap (s₀.mem.readW (addr (ctrP s₀) 12) 32) + arg s₀ 4)

theorem prologue_eq : saveRegs 5 ++ ctrSetup ++ keySetup = ([
    .mov .eax (.mem (at_ .esp 24)), .store (at_ .eax 256) .ebx, .store (at_ .eax 260) .esi,
    .store (at_ .eax 264) .edi, .store (at_ .eax 268) .ebp, .mov .edi (.reg .eax),
    .mov .ecx (.mem (at_ .esp 12)),
    .mov .eax (.mem (at_ .ecx 0)), .store (at_ .edi 272) .eax,
    .mov .eax (.mem (at_ .ecx 4)), .store (at_ .edi 276) .eax,
    .mov .eax (.mem (at_ .ecx 8)), .store (at_ .edi 280) .eax,
    .mov .eax (.mem (at_ .ecx 12)), .bswap .eax, .store (at_ .edi 284) .eax,
    .alu .add .eax (.mem (at_ .esp 20)), .bswap .eax, .store (at_ .ecx 12) .eax,
    .mov .esi (.mem (at_ .esp 8))] : List Instr) := rfl

theorem prologue_ok {s₀ : State} (hp : CPre s₀) :
    WP isa (.block (saveRegs 5 ++ ctrSetup ++ keySetup)) s₀ (P1 s₀) := by
  have fB := hp.fB; have fC := hp.fC; have fSp := hp.fSp
  let B := scrP s₀
  let C := ctrP s₀
  let E := s₀.gpr .esp
  have hwB : reg32 B 2048 ∈ s₀.wr := by
    rw [hp.wr]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))
  have hwC : reg32 C 16 ∈ s₀.wr := by rw [hp.wr]; exact List.mem_cons_self ..
  have hrA : argR s₀ ∈ s₀.rd := by rw [hp.rd]; simp
  -- The arguments are readable, and apart from the counter and the scratch buffer.
  have argC : ∀ i < 6, (argR s₀).Contains (addr E (4 + 4 * i)) 4 := fun i hi => by
    show (⟨addr E 4, 24⟩ : Region).Contains _ _
    exact part_contains (N := 28) (by omega) (by omega) (by omega) (by omega) (by decide)
  have argIn : ∀ (t : State), t.rd = s₀.rd → ∀ i < 6, InRegions (t.rd ++ t.wr) (addr E (4 + 4 * i)) 4 :=
    fun t ht i hi => ⟨argR s₀, List.mem_append_left _ (ht ▸ hrA), argC i hi⟩
  have bIn : ∀ (t : State), t.wr = s₀.wr → ∀ o, o + 4 ≤ 2048 → InRegions t.wr (addr B o) 4 :=
    fun t ht o ho => by rw [ht]; exact in_reg hwB fB ho (by decide)
  have cIn : ∀ (t : State), t.wr = s₀.wr → ∀ o, o + 4 ≤ 16 → InRegions t.wr (addr C o) 4 :=
    fun t ht o ho => by rw [ht]; exact in_reg hwC fC ho (by decide)
  have bC : ∀ o, o + 4 ≤ 2048 → (scrR s₀).Contains (addr B o) 4 := fun o ho => reg_contains fB ho (by decide)
  have cC : ∀ o, o + 4 ≤ 16 → (ctrR s₀).Contains (addr C o) 4 := fun o ho => reg_contains fC ho (by decide)
  rw [prologue_eq]
  refine wp_ldm (B := E) (o := 24) rfl (argIn _ rfl 5 (by omega)) fun s₁ u₁ => ?_
  have e₁ : s₁.gpr .eax = B := by rw [u₁.gpr]; rfl
  refine wp_stm e₁ (bIn _ u₁.wr 256 (by omega)) fun s₂ u₂ => ?_
  refine wp_stm (by rw [u₂.gpr]; exact e₁) (bIn _ (by rw [u₂.wr, u₁.wr]) 260 (by omega)) fun s₃ u₃ => ?_
  refine wp_stm (by rw [u₃.gpr, u₂.gpr]; exact e₁) (bIn _ (by rw [u₃.wr, u₂.wr, u₁.wr]) 264 (by omega))
    fun s₄ u₄ => ?_
  refine wp_stm (by rw [u₄.gpr, u₃.gpr, u₂.gpr]; exact e₁)
    (bIn _ (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]) 268 (by omega)) fun s₅ u₅ => ?_
  refine wp_mov fun s₆ u₆ => ?_
  have g₆ : ∀ r, r ≠ .eax → r ≠ .edi → s₆.gpr r = s₀.gpr r := fun r h1 h2 => by
    rw [u₆.other r h2, u₅.gpr, u₄.gpr, u₃.gpr, u₂.gpr, u₁.other r h1]
  have rd₆ : s₆.rd = s₀.rd := by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  have wr₆ : s₆.wr = s₀.wr := by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  have edi₆ : s₆.gpr .edi = B := by rw [u₆.gpr, u₅.gpr, u₄.gpr, u₃.gpr, u₂.gpr]; exact e₁
  -- The saves.
  let M₄ := (((s₀.mem.writeW (addr B 256) (s₀.gpr .ebx)).writeW (addr B 260) (s₀.gpr .esi)).writeW
    (addr B 264) (s₀.gpr .edi)).writeW (addr B 268) (s₀.gpr .ebp)
  have m₆ : s₆.mem = M₄ := by
    simp only [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₄.gpr, u₃.gpr, u₂.gpr]
    rw [u₁.other .ebx (by decide), u₁.other .esi (by decide), u₁.other .edi (by decide),
      u₁.other .ebp (by decide), u₁.mem]
  have f₆ : Frame [reg32 B 2048] s₀.mem s₆.mem := by
    rw [m₆]
    have hm := List.mem_singleton_self (reg32 B 2048)
    exact ((((Frame.refl _ _).writeW hm _ (bC 256 (by omega))).writeW hm _ (bC 260 (by omega))).writeW hm _
      (bC 264 (by omega))).writeW hm _ (bC 268 (by omega))
  -- The counter pointer.
  refine wp_ldm (B := E) (o := 12) (by rw [g₆ _ (by decide) (by decide)])
    (argIn _ rd₆ 2 (by omega)) fun s₇ u₇ => ?_
  have e₇ : s₇.gpr .ecx = C := by
    rw [u₇.gpr, f₆.readW (argC 2 (by omega)) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.aB) (by decide)]; rfl
  have dCB : ∀ r ∈ [reg32 B 2048], (ctrR s₀).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hp.dCB
  have dAB : ∀ r ∈ [reg32 B 2048], (argR s₀).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hp.aB
  have hm := List.mem_singleton_self (reg32 B 2048)
  -- The counter block's words.
  let c : Nat → BitVec 32 := fun o => s₀.mem.readW (addr C o) 32
  refine wp_ldm (B := C) (o := 0) e₇ (in_rd (cIn _ (by rw [u₇.wr, wr₆]) 0 (by omega))) fun s₈ u₈ => ?_
  have v₈ : s₈.gpr .eax = c 0 := by
    rw [u₈.gpr, u₇.mem]; exact f₆.readW (cC 0 (by omega)) dCB (by decide)
  have edi₈ : s₈.gpr .edi = B := by rw [u₈.other _ (by decide), u₇.other _ (by decide)]; exact edi₆
  refine wp_stm edi₈ (bIn _ (by rw [u₈.wr, u₇.wr, wr₆]) 272 (by omega)) fun s₉ u₉ => ?_
  have f₉ : Frame [reg32 B 2048] s₀.mem s₉.mem := by
    rw [u₉.mem, u₈.mem, u₇.mem]; exact f₆.writeW hm _ (bC 272 (by omega))
  have ecx₉ : s₉.gpr .ecx = C := by rw [u₉.gpr, u₈.other _ (by decide)]; exact e₇
  refine wp_ldm (B := C) (o := 4) ecx₉ (in_rd (cIn _ (by rw [u₉.wr, u₈.wr, u₇.wr, wr₆]) 4 (by omega)))
    fun s₁₀ u₁₀ => ?_
  have v₁₀ : s₁₀.gpr .eax = c 4 := by rw [u₁₀.gpr]; exact f₉.readW (cC 4 (by omega)) dCB (by decide)
  have edi₁₀ : s₁₀.gpr .edi = B := by rw [u₁₀.other _ (by decide), u₉.gpr]; exact edi₈
  refine wp_stm edi₁₀ (bIn _ (by rw [u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, wr₆]) 276 (by omega)) fun s₁₁ u₁₁ => ?_
  have f₁₁ : Frame [reg32 B 2048] s₀.mem s₁₁.mem := by
    rw [u₁₁.mem, u₁₀.mem]; exact f₉.writeW hm _ (bC 276 (by omega))
  have ecx₁₁ : s₁₁.gpr .ecx = C := by rw [u₁₁.gpr, u₁₀.other _ (by decide)]; exact ecx₉
  have wr₁₁ : s₁₁.wr = s₀.wr := by rw [u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, wr₆]
  have rd₁₁ : s₁₁.rd = s₀.rd := by rw [u₁₁.rd, u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, rd₆]
  refine wp_ldm (B := C) (o := 8) ecx₁₁ (in_rd (cIn _ wr₁₁ 8 (by omega))) fun s₁₂ u₁₂ => ?_
  have v₁₂ : s₁₂.gpr .eax = c 8 := by rw [u₁₂.gpr]; exact f₁₁.readW (cC 8 (by omega)) dCB (by decide)
  have edi₁₂ : s₁₂.gpr .edi = B := by
    rw [u₁₂.other _ (by decide), u₁₁.gpr, u₁₀.other _ (by decide), u₉.gpr]; exact edi₈
  refine wp_stm edi₁₂ (bIn _ (by rw [u₁₂.wr, wr₁₁]) 280 (by omega)) fun s₁₃ u₁₃ => ?_
  have f₁₃ : Frame [reg32 B 2048] s₀.mem s₁₃.mem := by
    rw [u₁₃.mem, u₁₂.mem]; exact f₁₁.writeW hm _ (bC 280 (by omega))
  have ecx₁₃ : s₁₃.gpr .ecx = C := by rw [u₁₃.gpr, u₁₂.other _ (by decide)]; exact ecx₁₁
  refine wp_ldm (B := C) (o := 12) ecx₁₃ (in_rd (cIn _ (by rw [u₁₃.wr, u₁₂.wr, wr₁₁]) 12 (by omega)))
    fun s₁₄ u₁₄ => wp_bswap fun s₁₅ u₁₅ => ?_
  have v₁₅ : s₁₅.gpr .eax = bswap (c 12) := by
    rw [u₁₅.gpr, u₁₄.gpr]; congr 1; exact f₁₃.readW (cC 12 (by omega)) dCB (by decide)
  have edi₁₅ : s₁₅.gpr .edi = B := by
    rw [u₁₅.other _ (by decide), u₁₄.other _ (by decide), u₁₃.gpr]; exact edi₁₂
  have wr₁₅ : s₁₅.wr = s₀.wr := by rw [u₁₅.wr, u₁₄.wr, u₁₃.wr, u₁₂.wr, wr₁₁]
  have rd₁₅ : s₁₅.rd = s₀.rd := by rw [u₁₅.rd, u₁₄.rd, u₁₃.rd, u₁₂.rd, rd₁₁]
  refine wp_stm edi₁₅ (bIn _ wr₁₅ 284 (by omega)) fun s₁₆ u₁₆ => ?_
  have f₁₆ : Frame [reg32 B 2048] s₀.mem s₁₆.mem := by
    rw [u₁₆.mem, u₁₅.mem, u₁₄.mem]; exact f₁₃.writeW hm _ (bC 284 (by omega))
  have esp₁₆ : s₁₆.gpr .esp = E := by
    rw [u₁₆.gpr, u₁₅.other _ (by decide), u₁₄.other _ (by decide), u₁₃.gpr, u₁₂.other _ (by decide),
      u₁₁.gpr, u₁₀.other _ (by decide), u₉.gpr, u₈.other _ (by decide), u₇.other _ (by decide),
      g₆ _ (by decide) (by decide)]
  refine wp_addm (B := E) (o := 20) esp₁₆
    (argIn _ (by rw [u₁₆.rd, rd₁₅]) 4 (by omega)) fun s₁₇ u₁₇ => wp_bswap fun s₁₈ u₁₈ => ?_
  have v₁₈ : s₁₈.gpr .eax = bswap (bswap (c 12) + arg s₀ 4) := by
    rw [u₁₈.gpr, u₁₇.gpr, u₁₆.gpr, v₁₅, arg_eq]
    congr 2
    exact f₁₆.readW (argC 4 (by omega)) dAB (by decide)
  have ecx₁₈ : s₁₈.gpr .ecx = C := by
    rw [u₁₈.other _ (by decide), u₁₇.other _ (by decide), u₁₆.gpr, u₁₅.other _ (by decide),
      u₁₄.other _ (by decide)]; exact ecx₁₃
  refine wp_stm ecx₁₈ (cIn _ (by rw [u₁₈.wr, u₁₇.wr, u₁₆.wr, wr₁₅]) 12 (by omega)) fun s₁₉ u₁₉ => ?_
  have esp₁₉ : s₁₉.gpr .esp = E := by
    rw [u₁₉.gpr, u₁₈.other .esp (by decide), u₁₇.other .esp (by decide)]; exact esp₁₆
  refine wp_ldm (B := E) (o := 8) esp₁₉ (argIn _ (by rw [u₁₉.rd, u₁₈.rd, u₁₇.rd, u₁₆.rd, rd₁₅]) 1 (by omega))
    fun s₂₀ u₂₀ => WP.block_nil ?_
  -- The memory at the end.
  let M₁₆ := ((((M₄.writeW (addr B 272) (c 0)).writeW (addr B 276) (c 4)).writeW (addr B 280) (c 8)).writeW
    (addr B 284) (bswap (c 12)))
  let M := M₁₆.writeW (addr C 12) (bswap (bswap (c 12) + arg s₀ 4))
  have m₂₀ : s₂₀.mem = M := by
    rw [u₂₀.mem, u₁₉.mem, v₁₈, u₁₈.mem, u₁₇.mem, u₁₆.mem, v₁₅, u₁₅.mem, u₁₄.mem, u₁₃.mem, v₁₂,
      u₁₂.mem, u₁₁.mem, v₁₀, u₁₀.mem, u₉.mem, v₈, u₈.mem, u₇.mem, m₆]
  have sC : (⟨addr B 256, 32⟩ : Region).Contains (addr B 256) (32 / 8) :=
    part_contains fB (by omega) (by omega) (by omega) (by decide)
  have hmB : (⟨addr B 256, 32⟩ : Region) ∈ [⟨addr B 256, 32⟩, ⟨addr C 12, 4⟩] := List.mem_cons_self ..
  have hmC : (⟨addr C 12, 4⟩ : Region) ∈ [⟨addr B 256, 32⟩, ⟨addr C 12, 4⟩] := by simp
  have cB : ∀ o, 256 ≤ o → o + 4 ≤ 288 → (⟨addr B 256, 32⟩ : Region).Contains (addr B o) (32 / 8) :=
    fun o h1 h2 => part_contains fB (by omega) h1 (by omega) (by decide)
  have fr : Frame [⟨addr B 256, 32⟩, ⟨addr C 12, 4⟩] s₀.mem s₂₀.mem := by
    rw [m₂₀]
    exact ((((((((Frame.refl _ _).writeW hmB _ (cB 256 (by omega) (by omega))).writeW hmB _
      (cB 260 (by omega) (by omega))).writeW hmB _ (cB 264 (by omega) (by omega))).writeW hmB _
      (cB 268 (by omega) (by omega))).writeW hmB _ (cB 272 (by omega) (by omega))).writeW hmB _
      (cB 276 (by omega) (by omega))).writeW hmB _ (cB 280 (by omega) (by omega))).writeW hmB _
      (cB 284 (by omega) (by omega)) |>.writeW hmC _ (Region.contains_self _ _)
  -- Reads of the scratch buffer through the write of the counter.
  have fB' : B.toNat + 2048 ≤ 2 ^ 32 := fB
  have rdB : ∀ o, o + 4 ≤ 2048 → M.readW (addr B o) 32 = M₁₆.readW (addr B o) 32 := fun o ho =>
    rd_wr_other hp.dCB.symm (bC o ho) (cC 12 (by omega))
  have g₂₀ : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edi → r ≠ .esi → s₂₀.gpr r = s₀.gpr r := by
    intro r h1 h2 h3 h4
    rw [u₂₀.other r h4, u₁₉.gpr, u₁₈.other r h1, u₁₇.other r h1, u₁₆.gpr, u₁₅.other r h1, u₁₄.other r h1,
      u₁₃.gpr, u₁₂.other r h1, u₁₁.gpr, u₁₀.other r h1, u₉.gpr, u₈.other r h1, u₇.other r h2,
      g₆ r h1 h3]
  refine ⟨g₂₀ _ (by decide) (by decide) (by decide) (by decide), ?_, ?_, ?_, ?_, fr, fun p hp' => ?_,
    fun v hv => ?_, ?_, ?_⟩
  · rw [u₂₀.other _ (by decide), u₁₉.gpr, u₁₈.other _ (by decide), u₁₇.other _ (by decide), u₁₆.gpr]
    exact edi₁₅
  · rw [u₂₀.gpr, ← u₂₀.mem, arg_eq]
    exact fr.readW (w := 32) (argC 1 (by omega)) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.aB.sub_right (part_sub_reg fB (by omega))
      · exact hp.aC.sub_right (part_sub_reg fC (by omega))) (by decide)
  · rw [u₂₀.rd, u₁₉.rd, u₁₈.rd, u₁₇.rd, u₁₆.rd, rd₁₅]
  · rw [u₂₀.wr, u₁₉.wr, u₁₈.wr, u₁₇.wr, u₁₆.wr, wr₁₅]
  · simp only [savedRegs, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl | rfl | rfl <;> rw [m₂₀, rdB _ (by omega)] <;>
      simp (disch := decide) only [M₁₆, M₄, rd_wr_ne fB', Mem.readW_writeW_self32]
  · rw [m₂₀]
    simp only [cw, cwOff]
    rw [rdB _ (by omega)]
    rcases (by omega : v = 0 ∨ v = 1 ∨ v = 2) with rfl | rfl | rfl <;>
      simp (disch := decide) only [M₁₆, M₄, rd_wr_ne fB', Mem.readW_writeW_self32] <;> rfl
  · rw [m₂₀]; simp only [cnum, cNum]; rw [rdB _ (by omega)]
    simp only [M₁₆, Mem.readW_writeW_self32]; rfl
  · rw [m₂₀]; exact Mem.readW_writeW_self32 _ _ _

/-! ## The counter block and the data, as blocks -/

/-- The counter, as the scratch buffer holds it. -/
theorem icb_lo (m : Mem) {C : BitVec 32} (hC : C.toNat + 16 ≤ 2 ^ 32) :
    bswap (m.readW (addr C 12) 32) = (Spec.Gcm.blockAt m (C.setWidth 64)).extractLsb' 0 32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro t ht
  have e : t = 8 * (t / 8) + t % 8 := by omega
  rw [e, bswap_bit _ (by omega) (by omega), BitVec.getLsbD_extractLsb', Nat.zero_add,
    decide_eq_true (by omega : 8 * (t / 8) + t % 8 < 32), Bool.true_and,
    show 8 * (t / 8) + t % 8 = 8 * (15 - (15 - t / 8)) + t % 8 by omega,
    blockAt_bit _ _ (by omega) (by omega), readW_bit _ _ (by omega) (by omega),
    addr_add64 (by omega), show 12 + (3 - t / 8) = 15 - t / 8 by omega, addr_eq (by omega)]

/-- The counter block's word `v < 3`, bit by bit. -/
theorem cw_bits (m : Mem) {C : BitVec 32} (hC : C.toNat + 16 ≤ 2 ^ 32) {v i j : Nat} (hv : v < 3)
    (hi : i < 4) (hj : j < 8) :
    (m.readW (addr C (4 * v)) 32).getLsbD (8 * i + j) =
      (Spec.Gcm.blockAt m (C.setWidth 64)).getLsbD (8 * (15 - (4 * v + i)) + j) := by
  rw [readW_bit _ _ hi hj, blockAt_bit _ _ (by omega) hj, addr_add64 (by omega), addr_eq (by omega)]

/-- The counter block after the prologue: its first twelve bytes, and the
last four big-endian `c + n`. -/
theorem ctr_after {m m' : Mem} {C : BitVec 32} (hC : C.toNat + 16 ≤ 2 ^ 32) {N : BitVec 32} {n : Nat}
    (hN : N = BitVec.ofNat 32 n)
    (h12 : ∀ k < 12, m' (addr C k) = m (addr C k))
    (hw : m'.readW (addr C 12) 32 = bswap (bswap (m.readW (addr C 12) 32) + N)) :
    Spec.Gcm.blockAt m' (C.setWidth 64) = Nat.repeat Spec.Gcm.inc32 n (Spec.Gcm.blockAt m (C.setWidth 64)) := by
  refine block_ext fun k hk => ?_
  rw [toBytes_blockAt _ _ hk, ctrBlock_byte _ _ hk, ← addr_eq (by omega)]
  split
  · rename_i h; rw [toBytes_blockAt _ _ hk, ← addr_eq (by omega), h12 k h]
  · rename_i h
    rw [← icb_lo m hC, ← hN]
    refine byte_ext fun j hj => ?_
    have := readW_bit m' (addr C 12) (i := k - 12) (t := j) (by omega) hj
    rw [addr_add64 (by omega), show 12 + (k - 12) = k by omega, hw, bswap_bit _ (by omega) hj] at this
    rw [← this, BitVec.getLsbD_extractLsb']
    simp only [hj, decide_true, Bool.true_and]
    congr 1; omega

theorem ctr32_of_dataInv {m₀ m : Mem} {D : Addr} {n R : Nat} {w : List Byte}
    {icb : Spec.Gcm.Block} (h : DataInv m₀ m D n (16 * n) (keyStream R w icb)) :
    Spec.Gcm.blocksAt m D n =
      Spec.Gcm.ctr32 (Spec.Gcm.aesWith R w) icb (Spec.Gcm.blocksAt m₀ D n) := by
  unfold Spec.Gcm.ctr32 Spec.Gcm.keystream Spec.Gcm.blocksAt
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_map, List.getElem_range, List.getElem_zipWith, List.length_map,
    List.length_range]
  simp only [List.length_map, List.length_range] at h1
  refine block_ext fun k hk => ?_
  rw [toBytes_xor _ _ hk, toBytes_blockAt _ _ hk, toBytes_blockAt _ _ hk, BitVec.add_assoc,
    ← BitVec.ofNat_add, h _ (by omega), ite_eq_left (by omega)]
  refine congrArg (_ ^^^ ·) ?_
  unfold Spec.Gcm.aesWith
  rw [toBytes_ofBytes (by simp) hk, keyStream, show (16 * i + k) / 16 = i by omega,
    show (16 * i + k) % 16 = k by omega, getD_eq _ hk, List.getD_eq_getElem?_getD,
    Vector.getElem?_toList, Vector.getElem?_eq_getElem hk, Option.getD_some]
  rfl

/-! ## Between the loops, and the epilogue -/

theorem groupSetup_ok {s : State} {B E : BitVec 32} (hb : s.gpr .edi = B) (he : s.gpr .esp = E)
    (hfit : B.toNat + 2048 ≤ 2 ^ 32) (hw : reg32 B 2048 ∈ s.wr)
    (hin : ∀ i, i = 3 ∨ i = 4 → InRegions (s.rd ++ s.wr) (addr E (4 + 4 * i)) 4)
    (hsep : ∀ i, i = 3 ∨ i = 4 → Region.Disjoint ⟨addr E (4 + 4 * i), 4⟩ (reg32 B 2048))
    {P : State → Prop}
    (h : ∀ s', s'.gpr .edi = B → s'.gpr .esp = E → (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) →
      s'.mem.readW (addr B dOff) 32 = s.mem.readW (addr E 16) 32 →
      s'.mem.readW (addr B nOff) 32 = s.mem.readW (addr E 20) 32 →
      s'.zf = some (s.mem.readW (addr E 20) 32 == 0) → Frame [⟨addr B dOff, 8⟩] s.mem s'.mem →
      s'.rd = s.rd → s'.wr = s.wr → P s') :
    WP isa (.block groupSetup) s P := by
  have hin' : ∀ (t : State), t.wr = s.wr → ∀ o, o + 4 ≤ 2048 → InRegions t.wr (addr B o) 4 :=
    fun t ht o ho => by rw [ht]; exact in_reg hw hfit ho (by decide)
  have hm : (⟨addr B dOff, 8⟩ : Region) ∈ [⟨addr B dOff, 8⟩] := List.mem_singleton_self _
  refine wp_ldm (B := E) (o := 16) he (hin 3 (.inl rfl)) fun s₁ u₁ => ?_
  refine wp_stm (B := B) (o := dOff) (by rw [u₁.other _ (by decide)]; exact hb) (hin' _ u₁.wr _ (by decide))
    fun s₂ u₂ => ?_
  have f₂ : Frame [⟨addr B dOff, 8⟩] s.mem s₂.mem := by
    rw [u₂.mem, u₁.mem]
    exact (Frame.refl _ _).writeW hm _ (part_contains hfit (by decide) (by decide) (by decide) (by decide))
  refine wp_ldm (B := E) (o := 20) (by rw [u₂.gpr, u₁.other _ (by decide)]; exact he)
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact hin 4 (.inr rfl)) fun s₃ u₃ => ?_
  refine wp_stm (B := B) (o := nOff) (by rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide)]; exact hb)
    (hin' _ (by rw [u₃.wr, u₂.wr, u₁.wr]) _ (by decide)) fun s₄ u₄ => wp_test fun s₅ u₅ hz => WP.block_nil ?_
  have v₃ : s₃.gpr .eax = s.mem.readW (addr E 20) 32 := by
    rw [u₃.gpr]
    exact f₂.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hsep 4 (.inr rfl)).sub_right (part_sub_reg hfit (by decide))) (by decide)
  have hfit' := hfit
  refine h s₅ ?_ ?_ (fun r hr => ?_) ?_ ?_ ?_ ?_ (by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd])
    (by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr])
  · rw [u₅.gpr, u₄.gpr, u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide)]; exact hb
  · rw [u₅.gpr, u₄.gpr, u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide)]; exact he
  · rw [u₅.gpr, u₄.gpr, u₃.other _ hr, u₂.gpr, u₁.other _ hr]
  · rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.gpr, u₁.mem,
      rd_wr_ne hfit _ _ (by decide) (by decide) (by decide) (by decide) (by decide),
      Mem.readW_writeW_self32]
  · rw [u₅.mem, u₄.mem, Mem.readW_writeW_self32, v₃]
  · rw [hz, u₄.gpr, v₃, BitVec.and_self]
  · rw [u₅.mem, u₄.mem, u₃.mem]
    exact f₂.writeW hm _ (part_contains hfit (by decide) (by decide) (by decide) (by decide))

theorem restore_ok {s : State} {B : BitVec 32} {N : Nat} (hb : s.gpr .edi = B) (hfit : B.toNat + N ≤ 2 ^ 32)
    (hw : reg32 B N ∈ s.wr) (hN : 272 ≤ N := by omega) :
    WP isa (.block restoreRegs) s fun s' =>
      (∀ p ∈ savedRegs, s'.gpr p.1 = s.mem.readW (addr B p.2) 32) ∧
      (∀ r, r ∉ [Reg.ebx, .esi, .edi, .ebp] → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem := by
  have hin : ∀ (t : State), t.rd = s.rd → t.wr = s.wr → ∀ o, o + 4 ≤ 272 →
      InRegions (t.rd ++ t.wr) (addr B o) 4 :=
    fun t h1 h2 o ho => by rw [h1, h2]; exact in_rd (in_reg hw hfit (by omega) (by decide))
  refine wp_ldm hb (hin _ rfl rfl 256 (by omega)) fun s₁ u₁ => ?_
  refine wp_ldm (by rw [u₁.other _ (by decide)]; exact hb) (hin _ u₁.rd u₁.wr 260 (by omega)) fun s₂ u₂ => ?_
  refine wp_ldm (by rw [u₂.other _ (by decide), u₁.other _ (by decide)]; exact hb)
    (hin _ (by rw [u₂.rd, u₁.rd]) (by rw [u₂.wr, u₁.wr]) 268 (by omega)) fun s₃ u₃ => ?_
  refine wp_ldm (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]; exact hb)
    (hin _ (by rw [u₃.rd, u₂.rd, u₁.rd]) (by rw [u₃.wr, u₂.wr, u₁.wr]) 264 (by omega))
    fun s₄ u₄ => WP.block_nil ⟨fun p hp => ?_, fun r hr => ?_, by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]⟩
  · simp only [savedRegs, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
    · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.mem]
    · rw [u₄.gpr, u₃.mem, u₂.mem, u₁.mem]
    · rw [u₄.other _ (by decide), u₃.gpr, u₂.mem, u₁.mem]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u₄.other _ hr.2.2.1, u₃.other _ hr.2.2.2, u₂.other _ hr.2.1, u₁.other _ hr.1]

/-! ## The whole function -/

theorem correct {s₀ : State} (hp : CPre s₀) :
    WP isa Impl.Aes.X86.ctr32 s₀ fun s' => abiPreserved s₀ s' ∧ Proof.Aes.ctr32X86.post s₀ s' := by
  have fB := hp.fB; have fC := hp.fC; have fD := hp.fD; have fS := hp.fS; have fSp := hp.fSp
  have hR : nRounds s₀ ≤ 14 := by rcases hp.rounds with h | h | h <;> omega
  let B := scrP s₀
  let C := ctrP s₀
  let D := datP s₀
  let S := schP s₀
  let E := s₀.gpr .esp
  let R := nRounds s₀
  let n := nBlk s₀
  let w := Spec.Aes.bytesAt s₀.mem (S.setWidth 64) (16 * (R + 1))
  let icb := Spec.Gcm.blockAt s₀.mem (C.setWidth 64)
  have fS' : S.toNat + 240 ≤ 2 ^ 32 := fS
  have fB' : B.toNat + 2048 ≤ 2 ^ 32 := fB
  have fC' : C.toNat + 16 ≤ 2 ^ 32 := fC
  have fD' : D.toNat + 16 * n ≤ 2 ^ 32 := fD
  have fE' : E.toNat + 28 ≤ 2 ^ 32 := fSp
  have hR' : R ≤ 14 := hR
  have hwB : reg32 B 2048 ∈ s₀.wr := by
    rw [hp.wr]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))
  have hwD : reg32 D (16 * n) ∈ s₀.wr := by
    rw [hp.wr]; exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
  have hrS : reg32 S 240 ∈ s₀.rd := by rw [hp.rd]; exact List.mem_cons_self ..
  have hrA : argR s₀ ∈ s₀.rd := by rw [hp.rd]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
  have argC : ∀ i < 6, (argR s₀).Contains (addr E (4 + 4 * i)) 4 := fun i hi => by
    show (⟨addr E 4, 24⟩ : Region).Contains _ _
    exact part_contains (N := 28) (by omega) (by omega) (by omega) (by omega) (by decide)
  have argIn : ∀ (t : State), t.rd = s₀.rd → ∀ i < 6, InRegions (t.rd ++ t.wr) (addr E (4 + 4 * i)) 4 :=
    fun t ht i hi => ⟨argR s₀, List.mem_append_left _ (ht ▸ hrA), argC i hi⟩
  -- The prologue.
  unfold Impl.Aes.X86.ctr32
  refine WP.seq (WP.mono (prologue_ok hp) fun s₁ h₁ => ?_)
  have F₁ := h₁.frame
  have d₁ : ∀ {r : Region}, r.Disjoint (scrR s₀) → r.Disjoint (ctrR s₀) →
      ∀ r' ∈ [(⟨addr B 256, 32⟩ : Region), ⟨addr C 12, 4⟩], r.Disjoint r' := by
    intro r h1 h2 r' hr'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl
    · exact h1.sub_right (part_sub_reg fB (by omega))
    · exact h2.sub_right (part_sub_reg fC (by omega))
  have arg₁ : ∀ i < 6, s₁.mem.readW (addr E (4 + 4 * i)) 32 = arg s₀ i := fun i hi =>
    F₁.readW (argC i hi) (d₁ hp.aB hp.aC) (by decide)
  have sched₁ : ∀ i < 240, s₁.mem (addr S i) = s₀.mem (addr S i) := fun i hi =>
    frame_one F₁ (reg_contains fS (by omega) (by decide)) (d₁ hp.dSB hp.dSC)
  have hk : KSetup s₁ B S R w :=
    { scr := by rw [h₁.wr]; exact hwB
      fitB := fB
      sch := by rw [h₁.rd]; exact List.mem_append_left _ hrS
      fitS := fS
      sep := hp.dSB
      rounds := hp.rounds
      base := h₁.edi
      argIn := fun i hi => by rw [h₁.esp]; exact argIn _ h₁.rd i (by omega)
      arg0 := by rw [h₁.esp]; exact arg₁ 0 (by omega)
      arg1 := by rw [h₁.esp, arg₁ 1 (by omega), BitVec.ofNat_toNat, BitVec.setWidth_eq]
      argSep := fun i hi => by rw [h₁.esp]; exact hp.aB.sub_left (part_sub (N := 28) (b := E) fSp (by omega)
        (by omega) (by omega))
      w := fun i hi => by
        rw [sched₁ i (by omega)]
        simp only [w, Spec.Aes.bytesAt, List.getD_eq_getElem?_getD, List.getElem?_map,
          List.getElem?_range hi, Option.map_some, Option.getD_some]
        rw [addr_eq (by have := fS'; omega)] }
  have hi₁ : KInv s₁ B R w R s₁ :=
    { hj := Nat.le_refl _
      esi := by rw [h₁.esi, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      rd := rfl
      wr := rfl
      keep := fun _ _ _ => rfl
      frame := Frame.refl _ _
      done := fun i h1 h2 => absurd h2 (by omega) }
  -- The key loop.
  refine WP.seq (WP.mono (keyLoop_ok hk hi₁) fun s₂ d₂ => ?_)
  have edi₂ : s₂.gpr .edi = B := (d₂.keep _ (by decide) (by decide)).trans h₁.edi
  have esp₂ : s₂.gpr .esp = E := (d₂.keep _ (by decide) (by decide)).trans h₁.esp
  have kfSub := hk.frame_sub
  have d₂' : ∀ {r : Region}, r.Disjoint (scrR s₀) → ∀ r' ∈ keyFrame B, r.Disjoint r' :=
    fun h r' hr' => h.sub_right (kfSub r' hr')
  have arg₂ : ∀ i < 6, s₂.mem.readW (addr E (4 + 4 * i)) 32 = arg s₀ i := fun i hi => by
    rw [← arg₁ i hi]; exact d₂.frame.readW (argC i hi) (d₂' hp.aB) (by decide)
  -- Between the loops.
  refine WP.seq (groupSetup_ok edi₂ esp₂ fB' (by rw [d₂.wr, h₁.wr]; exact hwB)
    (fun i hi => argIn _ (by rw [d₂.rd, h₁.rd]) i (by omega))
    (fun i hi => hp.aB.sub_left (part_sub (N := 28) (b := E) fSp (by omega) (by omega) (by omega)))
    fun s₃ edi₃ esp₃ g₃ ds₃ ns₃ z₃ F₃ rd₃ wr₃ => ?_)
  have F₃' : Frame [⟨addr B dOff, 8⟩] s₂.mem s₃.mem := F₃
  have d₃ : ∀ {r : Region}, r.Disjoint (scrR s₀) → ∀ r' ∈ [(⟨addr B dOff, 8⟩ : Region)], r.Disjoint r' :=
    fun h r' hr' => by
      simp only [List.mem_singleton] at hr'; subst hr'; exact h.sub_right (part_sub_reg fB (by decide))
  have arg₃ : ∀ i < 6, s₃.mem.readW (addr E (4 + 4 * i)) 32 = arg s₀ i := fun i hi => by
    rw [← arg₂ i hi]; exact F₃.readW (argC i hi) (d₃ hp.aB) (by decide)
  have e20 : s₂.mem.readW (addr E 20) 32 = arg s₀ 4 := arg₂ 4 (by omega)
  -- The regions the setup and the key loop wrote, all in the scratch buffer (or the counter).
  have hs : GSetup s₃ B D n R w icb :=
    { scr := by rw [wr₃, d₂.wr, h₁.wr]; exact hwB
      fitB := fB
      dat := by rw [wr₃, d₂.wr, h₁.wr]; exact hwD
      fitD := fD
      sep := hp.dDB
      rounds := hp.rounds
      argIn := by rw [esp₃]; exact argIn _ (by rw [rd₃, d₂.rd, h₁.rd]) 1 (by omega)
      argR := by rw [esp₃, arg₃ 1 (by omega), BitVec.ofNat_toNat, BitVec.setWidth_eq]
      argSep := by rw [esp₃]; exact hp.aB.sub_left (part_sub (N := 28) (b := E) fSp (by omega) (by omega)
        (by omega))
      argSepD := by rw [esp₃]; exact hp.aD.sub_left (part_sub (N := 28) (b := E) fSp (by omega) (by omega)
        (by omega))
      keys := fun j hj => by
        refine keyRel_congr (d₂.keys j hj) fun k hk => ?_
        have := keyOff_le (j := j) hR'
        exact F₃.readW (Region.contains_self _ _) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact part_disj fB (by simp only [lastKey] at this; omega) (by decide)
            (.inr (by simp only [dOff, lastKey] at this ⊢; omega))) (by decide)
      cw := fun v hv i hi j hj => by
        have e : cw s₃.mem B v = cw s₁.mem B v := by
          simp only [cw, cwOff]
          rw [F₃.readW (Region.contains_self _ _) (fun r hr => by
              simp only [List.mem_singleton] at hr; subst hr
              exact part_disj fB (by omega) (by decide) (.inl (by simp only [dOff]; omega))) (by decide)]
          exact d₂.frame.readW (Region.contains_self _ _) (fun r hr => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
            rcases hr with rfl | rfl
            · show Region.Disjoint _ ⟨B.setWidth 64, 256⟩
              rw [← addr_zero]; exact part_disj fB (by omega) (by omega) (.inr (by omega))
            · exact part_disj fB (by omega) (by omega) (.inl (by omega))) (by decide)
        rw [e, h₁.cw v hv]; exact cw_bits _ fC hv hi hj }
  -- The memory the prologue, the key loop and the setup of the groups wrote.
  have dScr : ∀ {r : Region}, r.Disjoint (scrR s₀) → r.Disjoint (ctrR s₀) → ∀ {m' : Mem},
      Frame [⟨addr B dOff, 8⟩] s₂.mem m' → Frame [scrR s₀, ctrR s₀] s₀.mem m' := by
    intro r _ _ m' hf
    refine (F₁.sub fun r hr => ?_).trans ((d₂.frame.sub fun r hr => ?_).trans (hf.sub fun r hr => ?_))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨scrR s₀, by simp, part_sub_reg fB (by omega)⟩
      · exact ⟨ctrR s₀, by simp, part_sub_reg fC (by omega)⟩
    · exact ⟨scrR s₀, by simp, kfSub r hr⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scrR s₀, by simp, part_sub_reg fB (by decide)⟩
  have G₃ : Frame [scrR s₀, ctrR s₀] s₀.mem s₃.mem := dScr hp.dDB hp.dCD.symm F₃
  have num₃ : cnum s₃.mem B = icb.extractLsb' 0 32 := by
    rw [← icb_lo _ fC, ← h₁.cnum]
    simp only [cnum, cNum]
    rw [F₃.readW (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact part_disj fB (by omega) (by decide) (.inl (by decide))) (by decide)]
    exact d₂.frame.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · show Region.Disjoint _ ⟨B.setWidth 64, 256⟩
        rw [← addr_zero]; exact part_disj fB (by omega) (by omega) (.inr (by omega))
      · exact part_disj fB (by omega) (by omega) (.inl (by omega))) (by decide)
  have dD : ∀ r ∈ [scrR s₀, ctrR s₀], (datR s₀).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.dDB
    · exact hp.dCD.symm
  have data₃ : DataInv s₀.mem s₃.mem (D.setWidth 64) n 0 (keyStream R w icb) := fun i hi => by
    rw [ite_eq_right (show ¬ i < 0 by omega)]
    exact (G₃.bytes (R := datR s₀) dD (by show 16 * n ≤ 2 ^ 64; omega) hi).trans (by simp; rfl)
  -- The groups.
  refine WP.seq (WP.mono (Q := GDone s₀.mem s₃ B D n R w icb) ?_ fun s₄ h₄ => ?_)
  · refine WP.ite (arg s₀ 4 == 0) (by simp only [X86.eval, z₃, e20]) (fun hb => ?_) (fun hb => ?_)
    · have hn0 : n = 0 := by
        have : arg s₀ 4 = 0 := by simpa using hb
        show (arg s₀ 4).toNat = 0; rw [this]; rfl
      exact WP.block_nil ⟨edi₃, rfl, rfl, rfl, Frame.refl _ _, fun i hi => absurd hi (by omega)⟩
    · have hn0 : 0 < n := by
        have : arg s₀ 4 ≠ 0 := by simpa using hb
        show 0 < (arg s₀ 4).toNat
        exact Nat.pos_of_ne_zero fun h => this (BitVec.eq_of_toNat_eq (by simpa using h))
      refine groups_ok hs ⟨by omega, edi₃, rfl, rfl, rfl, Frame.refl _ _, by rw [num₃]; simp, ?_, ?_,
        by simpa using data₃⟩
      · rw [ds₃, arg₂ 3 (by omega)]; simp; rfl
      · rw [ns₃, e20, Nat.mul_zero, Nat.sub_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · -- The epilogue.
    refine WP.mono (restore_ok h₄.base fB' (by rw [h₄.wr, wr₃, d₂.wr, h₁.wr]; exact hwB))
      fun s₅ ⟨sv₅, o₅, m₅⟩ => ?_
    have G₄ : Frame [scrR s₀, ctrR s₀, datR s₀] s₀.mem s₄.mem := by
      refine (G₃.mono (by simp)).trans (h₄.frame.sub fun r hr => ?_)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨scrR s₀, by simp, Region.sub_prefix (by omega)⟩
      · exact ⟨scrR s₀, by simp, part_sub_reg fB (by decide)⟩
      · exact ⟨datR s₀, by simp, fun _ h => h⟩
    have retD : ∀ r ∈ [scrR s₀, ctrR s₀, datR s₀], (retR s₀).Disjoint r := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hp.rB
      · exact hp.rC
      · exact hp.rD
    -- The saved registers.
    have saved : ∀ p ∈ savedRegs, s₄.mem.readW (addr B p.2) 32 = s₀.gpr p.1 := by
      intro p hp'
      have ho : 256 ≤ p.2 ∧ p.2 + 4 ≤ 272 := by
        simp only [savedRegs, List.mem_cons, List.not_mem_nil, or_false] at hp'
        rcases hp' with rfl | rfl | rfl | rfl <;> decide
      rw [← h₁.saved p hp']
      have e₄ : s₄.mem.readW (addr B p.2) 32 = s₃.mem.readW (addr B p.2) 32 :=
        h₄.frame.readW (Region.contains_self _ _) (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · show Region.Disjoint _ ⟨B.setWidth 64, 256⟩
            rw [← addr_zero]; exact part_disj fB (by omega) (by omega) (.inr (by omega))
          · exact part_disj fB (by omega) (by decide) (.inl (by simp only [cNum]; omega))
          · exact (hp.dDB.sub_right (part_sub_reg fB (by omega))).symm) (by decide)
      rw [e₄, F₃.readW (Region.contains_self _ _) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact part_disj fB (by omega) (by decide) (.inl (by simp only [dOff]; omega))) (by decide)]
      exact d₂.frame.readW (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · show Region.Disjoint _ ⟨B.setWidth 64, 256⟩
          rw [← addr_zero]; exact part_disj fB (by omega) (by omega) (.inr (by omega))
        · exact part_disj fB (by omega) (by omega) (.inl (by omega))) (by decide)
    have esp₄ : s₄.gpr .esp = E := h₄.esp.trans esp₃
    refine ⟨⟨fun r hr => ?_, ?_⟩, ?_, ?_⟩
    · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · rw [sv₅ (.ebx, 256) (by simp [savedRegs]), saved (.ebx, 256) (by simp [savedRegs])]
      · rw [sv₅ (.esi, 260) (by simp [savedRegs]), saved (.esi, 260) (by simp [savedRegs])]
      · rw [sv₅ (.edi, 264) (by simp [savedRegs]), saved (.edi, 264) (by simp [savedRegs])]
      · rw [sv₅ (.ebp, 268) (by simp [savedRegs]), saved (.ebp, 268) (by simp [savedRegs])]
      · rw [o₅ _ (by simp), esp₄]
    · rw [m₅]
      exact G₄.readW (Region.contains_self _ _) retD (by decide)
    · show Spec.Gcm.blocksAt s₅.mem (D.setWidth 64) n = _
      rw [m₅]; exact ctr32_of_dataInv h₄.data
    · show Spec.Gcm.blockAt s₅.mem (C.setWidth 64) = Nat.repeat Spec.Gcm.inc32 n icb
      have e : Spec.Gcm.blockAt s₅.mem (C.setWidth 64) = Spec.Gcm.blockAt s₁.mem (C.setWidth 64) := by
        refine Proof.Gcm.blockAt_congr fun k hk => ?_
        rw [m₅]
        have H : Frame [scrR s₀, datR s₀] s₁.mem s₄.mem := by
          refine (d₂.frame.sub fun r hr => ⟨scrR s₀, by simp, kfSub r hr⟩).trans
            ((F₃.sub fun r hr => ⟨scrR s₀, by simp, by
              simp only [List.mem_singleton] at hr; subst hr; exact part_sub_reg fB (by decide)⟩).trans
            (h₄.frame.sub fun r hr => ?_))
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · exact ⟨scrR s₀, by simp, Region.sub_prefix (by omega)⟩
          · exact ⟨scrR s₀, by simp, part_sub_reg fB (by decide)⟩
          · exact ⟨datR s₀, by simp, fun _ h => h⟩
        exact H.bytes (R := ctrR s₀) (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact hp.dCB
          · exact hp.dCD) (by show 16 ≤ 2 ^ 64; decide) hk
      rw [e]
      refine ctr_after fC (N := arg s₀ 4) (by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]) (fun k hk => ?_)
        h₁.ctr
      refine frame_one (r := ⟨addr C k, 1⟩) F₁ (Region.contains_self _ _) fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (hp.dCB.sub_left (part_sub_reg fC (by omega))).sub_right (part_sub_reg fB (by omega))
      · exact part_disj fC (N := 16) (by omega) (by omega) (.inl (by omega))

/-- Memory holding the arguments `0x1000, 10, 0x2000, 0x3000, 0, 0x4000` at `0x8004`. -/
def ctrSatMem : Mem := fun a =>
  if a = 0x8005 then 0x10 else if a = 0x8008 then 10 else if a = 0x800D then 0x20
  else if a = 0x8011 then 0x30 else if a = 0x8019 then 0x40 else 0

/-- A state satisfying the precondition (with no data). -/
def ctrSat : State where
  gpr r := match r with
    | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := ctrSatMem
  rd := [⟨0x1000, 240⟩, ⟨0x8004, 24⟩]
  wr := [⟨0x2000, 16⟩, ⟨0x3000, 0⟩, ⟨0x4000, 2048⟩]

theorem ctr32_correct (s : State) (hs : Proof.Aes.ctr32X86.pre s) :
    ∃ t s', Exec isa Impl.Aes.X86.ctr32 s t s' ∧ abiPreserved s s' ∧ Proof.Aes.ctr32X86.post s s' :=
  (correct (CPre.of hs)).imp fun _ ⟨s', he, h⟩ => ⟨s', he, h⟩

theorem ctr32_verified :
    Verified X86.target Impl.Aes.X86.ctr32 (Spec.Gcm.ctr32Contract X86.abi) :=
  Verified.of_correct ctr32_correct ctr32_ct
    (by
      have a0 : arg ctrSat 0 = 0x1000 := by decide
      have a1 : arg ctrSat 1 = 10 := by decide
      have a2 : arg ctrSat 2 = 0x2000 := by decide
      have a3 : arg ctrSat 3 = 0x3000 := by decide
      have a4 : arg ctrSat 4 = 0 := by decide
      have a5 : arg ctrSat 5 = 0x4000 := by decide
      have e : argAddr ctrSat 0 = 0x8004 := by decide
      have esp : ctrSat.gpr .esp = 0x8000 := rfl
      sig_implies [Spec.Gcm.ctr32Contract, Spec.Gcm.ctr32Sig, X86.abi, X86.argSlots,
        X86.argVal, X86.argBytes, Proof.Aes.ctr32X86] [a0, a1, a2, a3, a4, a5, e, esp] using ctrSat)

end VG.Proof.Aes.X86
