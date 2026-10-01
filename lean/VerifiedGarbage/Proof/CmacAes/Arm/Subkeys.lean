import VerifiedGarbage.Proof.CmacAes.Arm.Dbl
import VerifiedGarbage.Proof.CmacAes.Arm.UpdateCorrect

/-!
# AES-CMAC on ARMv7: `vg_cmac_aes_subkeys`

Untrusted: everything here is checked by Lean. `L = CIPH_K(0)` is computed
into the first block of the subkeys (a zero counter block and a zero data
block), then doubled there (`K1`) and into the second block (`K2`).
-/

namespace VG.Proof.CmacAes.Arm

open VG VG.Arm VG.Impl.CmacAes.Arm
open VG.Proof.MdStream.Arm (Upd Mupd op2_imm op2_reg wp_mov wp_add wp_ldr saveMem saveList_ok saveMem_frame
  readW_writeW_save)

section
variable (s₀ : State)

/-- The subkeys. -/
abbrev Kb : BitVec 32 := s₀.gpr .r2
/-- The scratch buffer. -/
abbrev Sc : BitVec 32 := s₀.gpr .r3

abbrev kR : Region := ⟨State.addr (Kb s₀), 32⟩
abbrev scR : Region := ⟨State.addr (Sc s₀), 2176⟩

end

/-- The precondition, by name. -/
structure SPre (s₀ : State) : Prop where
  rd : s₀.rd = [schR s₀]
  wr : s₀.wr = [kR s₀, scR s₀]
  sch_k : (schR s₀).Disjoint (kR s₀)
  sch_scr : (schR s₀).Disjoint (scR s₀)
  k_scr : (kR s₀).Disjoint (scR s₀)
  b_sch : (belowR s₀).Disjoint (schR s₀)
  b_k : (belowR s₀).Disjoint (kR s₀)
  b_scr : (belowR s₀).Disjoint (scR s₀)
  sch_fit : (W s₀).toNat + 240 ≤ 2 ^ 32
  k_fit : (Kb s₀).toNat + 32 ≤ 2 ^ 32
  scr_fit : (Sc s₀).toNat + 2176 ≤ 2 ^ 32
  sp8 : 8 ≤ s₀.sp.toNat
  rounds : R s₀ = 10 ∨ R s₀ = 12 ∨ R s₀ = 14

theorem SPre.of {s₀ : State} (h : subkeysArm.pre s₀) : SPre s₀ :=
  let ⟨a, b, c, d, e, f, g, h, i, j, k, l, m⟩ := h
  ⟨a, b, c, d, e, f, g, h, i, j, k, l, m⟩

/-- The registers `subkeys` saves, and where. -/
def saved4 : List (Reg × Nat) := [(.r4, 2064), (.r5, 2068), (.r6, 2072), (.lr, 2076)]

theorem subkeysPre_eq : subkeysPre = saved4.map (fun p => Instr.str p.1 .r3 p.2) ++
    (.mov .r6 (.reg .r2) :: .mov .r5 (.reg .r3) :: .mov .r12 (.imm 0) :: (zeroBlk .r12 .r3 2048 ++
      (zeroBlk .r12 .r2 0 ++ ([.dp .add .r2 .r5 (.imm (BitVec.ofNat 32 2048)), .mov .r3 (.reg .r6),
        .mov .r4 (.imm 1)] : List Instr)))) := rfl

theorem subkeysPost_eq : subkeysPost = dbl 0 0 ++ (dbl 0 16 ++
    ([(.r4, 2064), (.r6, 2072), (.lr, 2076)].map (fun (p : Reg × Nat) => Instr.ldr p.1 .r5 p.2) ++
      ([.ldr .r5 .r5 2068] : List Instr))) := rfl

set_option simprocs false in
theorem saved4_slot (m : Mem) (B : Addr) (g : Reg → BitVec 32) {r : Reg} {d : Nat} (h : (r, d) ∈ saved4) :
    (saveMem m B g saved4).readW (B + BitVec.ofNat 64 d) 32 = g r := by
  simp only [saved4, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
  simp (disch := decide) only [saved4, saveMem, Mem.readW_writeW_self32, readW_writeW_save]

/-- The memory before the call. -/
def preMem (s₀ : State) : Mem :=
  Proof.Cmac.zero4 (Proof.Cmac.zero4 (saveMem s₀.mem (State.addr (Sc s₀)) s₀.gpr saved4)
    (State.addr (Sc s₀) + BitVec.ofNat 64 2048)) (State.addr (Kb s₀))

/-- What the code before the call leaves. -/
structure SAfter (s₀ s : State) : Prop where
  pre : CallPre s (W s₀) (Sc s₀ + BitVec.ofNat 32 2048) (Kb s₀) (Sc s₀) (R s₀) .r4 .r5
  keep : ∀ r, r ≠ .r2 → r ≠ .r3 → r ≠ .r4 → r ≠ .r5 → r ≠ .r6 → r ≠ .r12 → s.gpr r = s₀.gpr r
  r5 : s.gpr .r5 = Sc s₀
  r6 : s.gpr .r6 = Kb s₀
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : s.mem = preMem s₀

theorem pre_wp {s₀ : State} (hp : SPre s₀) : WP isa (.block subkeysPre) s₀ (SAfter s₀) := by
  have kf := hp.k_fit
  have sf := hp.scr_fit
  have sf' : (s₀.gpr .r3).toNat + 2176 ≤ 2 ^ 32 := sf
  have hR := hp.rounds
  have hRb : 16 * (R s₀ + 1) ≤ 240 := by rcases hR with h | h | h <;> omega
  have cK : ∀ d n, d + n ≤ 32 → Covers [⟨State.addr (Kb s₀) + BitVec.ofNat 64 d, n⟩] s₀.wr := fun d n h => by
    rw [hp.wr]
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨kR s₀, by simp, d, rfl, h⟩
  have cS : ∀ d n, d + n ≤ 2176 → Covers [⟨State.addr (Sc s₀) + BitVec.ofNat 64 d, n⟩] s₀.wr := fun d n h => by
    rw [hp.wr]
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨scR s₀, by simp, d, rfl, h⟩
  have rw' : ∀ {rs a n}, Covers rs s₀.wr → InRegions rs a n → InRegions (s₀.rd ++ s₀.wr) a n :=
    fun h hi => by obtain ⟨r, hr, hc⟩ := h _ _ hi; exact ⟨r, List.mem_append_right _ hr, hc⟩
  have cKr : ∀ d n, d + n ≤ 32 → Covers [⟨State.addr (Kb s₀) + BitVec.ofNat 64 d, n⟩] (s₀.rd ++ s₀.wr) :=
    fun d n h a k hi => rw' (cK d n h) hi
  have aS : ∀ {d}, d < 2176 → State.addr (Sc s₀ + BitVec.ofNat 32 d) = State.addr (Sc s₀) + BitVec.ofNat 64 d :=
    fun _ => addr_add (by omega)
  -- Before the call.
  rw [subkeysPre_eq]
  refine saveList_ok saved4 s₀ _ (fun p hp' => ?_) fun s₁ g₁ rd₁ wr₁ sp₁ m₁ => ?_
  · have hb : 2064 ≤ p.2 ∧ p.2 + 4 ≤ 2080 := by
      simp only [saved4, List.mem_cons, List.not_mem_nil, or_false] at hp'
      rcases hp' with rfl | rfl | rfl | rfl <;> decide
    exact ⟨by omega, by omega, cS p.2 4 (by omega) _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩⟩
  refine wp_mov (op2_reg _ _) fun s₂ u₂ => wp_mov (op2_reg _ _) fun s₃ u₃ =>
    wp_mov (op2_imm (by decide)) fun s₄ u₄ => ?_
  have r3₄ : s₄.gpr .r3 = Sc s₀ := by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), g₁]
  refine Proof.CmacAes.Arm.zeroBlk_ok u₄.gpr (by decide) (by rw [r3₄]; omega)
    (by rw [r3₄, u₄.wr, u₃.wr, u₂.wr, wr₁]; exact cS 2048 16 (by decide)) fun s₅ G₅ m₅ rd₅ wr₅ sp₅ => ?_
  have r2₅ : s₅.gpr .r2 = Kb s₀ := by
    rw [G₅, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), g₁]
  refine Proof.CmacAes.Arm.zeroBlk_ok (by rw [G₅, u₄.gpr]) (by decide) (by rw [r2₅]; omega)
    (by rw [r2₅, add0, wr₅, u₄.wr, u₃.wr, u₂.wr, wr₁]; simpa using cK 0 16 (by decide))
    fun s₆ G₆ m₆ rd₆ wr₆ sp₆ => ?_
  refine wp_add (op2_imm (by decide)) fun s₇ u₇ => wp_mov (op2_reg _ _) fun s₈ u₈ =>
    wp_mov (op2_imm (by decide)) fun s₉ u₉ => WP.block_nil ?_
  have keep₉ : ∀ r, r ≠ .r2 → r ≠ .r3 → r ≠ .r4 → r ≠ .r5 → r ≠ .r6 → r ≠ .r12 → s₉.gpr r = s₀.gpr r :=
    fun r h2 h3 h4 h5 h6 h12 => by
      rw [u₉.other _ h4, u₈.other _ h3, u₇.other _ h2, G₆, G₅, u₄.other _ h12, u₃.other _ h5, u₂.other _ h6, g₁]
  have r5₉ : s₉.gpr .r5 = Sc s₀ := by
    rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), G₆, G₅, u₄.other _ (by decide),
      u₃.gpr, u₂.other _ (by decide), g₁]
  have r6₉ : s₉.gpr .r6 = Kb s₀ := by
    rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), G₆, G₅, u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.gpr, g₁]
  have sp₉ : s₉.sp = s₀.sp := by rw [u₉.sp, u₈.sp, u₇.sp, sp₆, sp₅, u₄.sp, u₃.sp, u₂.sp, sp₁]
  have rd₉ : s₉.rd = s₀.rd := by rw [u₉.rd, u₈.rd, u₇.rd, rd₆, rd₅, u₄.rd, u₃.rd, u₂.rd, rd₁]
  have wr₉ : s₉.wr = s₀.wr := by rw [u₉.wr, u₈.wr, u₇.wr, wr₆, wr₅, u₄.wr, u₃.wr, u₂.wr, wr₁]
  have mem₉ : s₉.mem = preMem s₀ := by
    rw [u₉.mem, u₈.mem, u₇.mem, m₆, r2₅, add0, m₅, r3₄, u₄.mem, u₃.mem, u₂.mem, m₁]; rfl
  -- The memory before the call.
  have cA : State.addr (Sc s₀ + BitVec.ofNat 32 2048) = State.addr (Sc s₀) + BitVec.ofNat 64 2048 := aS (by decide)
  have kC : (⟨State.addr (Kb s₀), 16⟩ : Region).Disjoint ⟨State.addr (Sc s₀) + BitVec.ofNat 64 2048, 16⟩ :=
    (hp.k_scr.sub_left (Region.sub_prefix (by decide))).sub_right (Offset.sub_base _ (by decide))
  have hb : below s₉ = belowR s₀ := by rw [below, sp₉]; rfl
  have pre : CallPre s₉ (W s₀) (Sc s₀ + BitVec.ofNat 32 2048) (Kb s₀) (Sc s₀) (R s₀) .r4 .r5 :=
    { r0 := keep₉ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      r1 := by
        rw [keep₉ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; simp [R]
      r2 := by
        rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr, G₆, G₅, u₄.other _ (by decide), u₃.gpr,
          u₂.other _ (by decide), g₁]
      r3 := by rw [u₉.other _ (by decide), u₈.gpr, u₇.other _ (by decide), G₆, G₅, u₄.other _ (by decide),
          u₃.other _ (by decide), u₂.gpr, g₁]
      hra := u₉.gpr
      hrb := r5₉
      regs := by decide
      rounds := hR
      hsp := by rw [sp₉]; exact hp.sp8
      wc := by rw [cA]; exact hp.sch_scr.sub_right (Offset.sub_base _ (by decide))
      wd := hp.sch_k.sub_right (Region.sub_prefix (by decide))
      ws := hp.sch_scr.sub_right (Region.sub_prefix (by decide))
      cd := by rw [cA]; exact kC.symm
      cs := by rw [cA]; exact Offset.disjoint_base _ (by decide) (by omega)
      ds := (hp.k_scr.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide))
      bw := by rw [hb]; exact hp.b_sch
      bc := by rw [hb, cA]; exact hp.b_scr.sub_right (Offset.sub_base _ (by decide))
      bd := by rw [hb]; exact hp.b_k.sub_right (Region.sub_prefix (by decide))
      bs := by rw [hb]; exact hp.b_scr.sub_right (Region.sub_prefix (by decide))
      hW := hp.sch_fit
      hC := by
        rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 2048) (by decide),
          Nat.mod_eq_of_lt (by omega)]; omega
      hD := by omega
      hS := by omega
      reads := by
        rw [rd₉, wr₉, hp.rd]
        exact Covers.of_sub fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact ⟨schR s₀, by simp, 0, by simp, by simp⟩
      writes := by
        rw [wr₉, hp.wr, cA]
        refine Covers.of_sub fun r hr => ?_
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact ⟨scR s₀, by simp, 2048, rfl, by simp⟩
        · exact ⟨kR s₀, by simp, 0, by simp, by simp⟩
        · exact ⟨scR s₀, by simp, 0, by simp, by simp⟩
      zero := by rw [mem₉, preMem]; exact Proof.Cmac.zero4_bytes _ _ }
  exact ⟨pre, keep₉, r5₉, r6₉, sp₉, rd₉, wr₉, mem₉⟩

theorem subkeys_wp {s₀ : State} (h0 : subkeysArm.pre s₀) :
    WP isa subkeys s₀ fun s' => abiPreserved s₀ s' ∧ subkeysArm.post s₀ s' := by
  have hp := SPre.of h0
  have kf := hp.k_fit
  have sf := hp.scr_fit
  have sf' : (s₀.gpr .r3).toNat + 2176 ≤ 2 ^ 32 := sf
  have hR := hp.rounds
  have hRb : 16 * (R s₀ + 1) ≤ 240 := by rcases hR with h | h | h <;> omega
  have cK : ∀ d n, d + n ≤ 32 → Covers [⟨State.addr (Kb s₀) + BitVec.ofNat 64 d, n⟩] s₀.wr := fun d n h => by
    rw [hp.wr]
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨kR s₀, by simp, d, rfl, h⟩
  have cS : ∀ d n, d + n ≤ 2176 → Covers [⟨State.addr (Sc s₀) + BitVec.ofNat 64 d, n⟩] s₀.wr := fun d n h => by
    rw [hp.wr]
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨scR s₀, by simp, d, rfl, h⟩
  have rw' : ∀ {rs a n}, Covers rs s₀.wr → InRegions rs a n → InRegions (s₀.rd ++ s₀.wr) a n :=
    fun h hi => by obtain ⟨r, hr, hc⟩ := h _ _ hi; exact ⟨r, List.mem_append_right _ hr, hc⟩
  have cKr : ∀ d n, d + n ≤ 32 → Covers [⟨State.addr (Kb s₀) + BitVec.ofNat 64 d, n⟩] (s₀.rd ++ s₀.wr) :=
    fun d n h a k hi => rw' (cK d n h) hi
  have aS : ∀ {d}, d < 2176 → State.addr (Sc s₀ + BitVec.ofNat 32 d) = State.addr (Sc s₀) + BitVec.ofNat 64 d :=
    fun _ => addr_add (by omega)
  unfold subkeys
  refine WP.seq (WP.mono (pre_wp hp) fun s₉ a => ?_)
  obtain ⟨pre, keep₉, r5₉, r6₉, sp₉, rd₉, wr₉, mem₉⟩ := a
  -- The memory before the call.
  have cA : State.addr (Sc s₀ + BitVec.ofNat 32 2048) = State.addr (Sc s₀) + BitVec.ofNat 64 2048 := aS (by decide)
  have kC : (⟨State.addr (Kb s₀), 16⟩ : Region).Disjoint ⟨State.addr (Sc s₀) + BitVec.ofNat 64 2048, 16⟩ :=
    (hp.k_scr.sub_left (Region.sub_prefix (by decide))).sub_right (Offset.sub_base _ (by decide))
  have f₉ : Frame [scR s₀, kR s₀] s₀.mem s₉.mem := by
    rw [mem₉, preMem]
    refine (((saveMem_frame _ _ _ (L := 2176) (by decide) saved4 (by decide)).sub fun r hr => ?_).trans
      ((Proof.Cmac.frame_store4 _ _ _ _ _).sub fun r hr => ?_)).trans
      ((Proof.Cmac.frame_store4 _ _ _ _ _).sub fun r hr => ?_) <;>
    simp only [List.mem_singleton] at hr <;> subst hr
    · exact ⟨scR s₀, by simp, fun _ h => h⟩
    · exact ⟨scR s₀, by simp, Offset.sub_base _ (by decide)⟩
    · exact ⟨kR s₀, by simp, Region.sub_prefix (by decide)⟩
  have zC : Spec.Aes.bytesAt s₉.mem (State.addr (Sc s₀) + BitVec.ofNat 64 2048) 16 = Spec.Cmac.zeros 16 := by
    rw [mem₉, preMem, Proof.Cmac.zero4, Proof.Cmac.bytesAt_frame16 (Proof.Cmac.frame_store4 _ _ _ _ _) (by
      intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact kC.symm)]
    exact Proof.Cmac.zero4_bytes _ _
  have hb : below s₉ = belowR s₀ := by rw [below, sp₉]; rfl
  -- The call.
  refine WP.seq (WP.mono (ctr_call pre) fun s₁₀ h₁₀ => ?_)
  have sv (r : Reg) (hr : r ∈ preserved) (hlr : r ≠ .lr) : s₁₀.gpr r = s₉.gpr r := h₁₀.saved r hr hlr
  have r6₁₀ : s₁₀.gpr .r6 = Kb s₀ := by rw [sv .r6 (by simp [preserved]) (by decide), r6₉]
  have rdwr₁₀ : s₁₀.rd ++ s₁₀.wr = s₀.rd ++ s₀.wr := by rw [h₁₀.rd, h₁₀.wr, rd₉, wr₉]
  have wr₁₀ : s₁₀.wr = s₀.wr := by rw [h₁₀.wr, wr₉]
  have L : Spec.Aes.bytesAt s₁₀.mem (State.addr (Kb s₀)) 16 = ciph s₀ (Spec.Cmac.zeros 16) := by
    rw [h₁₀.out, cA, zC, Proof.Cmac.bytesAt_frame f₉ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.sch_scr.sub_left (Region.sub_prefix hRb)
      · exact hp.sch_k.sub_left (Region.sub_prefix hRb)) (by omega)]
  -- After the call.
  rw [subkeysPost_eq]
  refine dbl_wp r6₁₀ (by decide) (by decide) (by omega) (by omega)
    (by rw [rdwr₁₀]; exact cKr 0 16 (by decide)) (by rw [wr₁₀]; exact cK 0 16 (by decide))
    fun s₁₁ g₁₁ m₁₁ rd₁₁ wr₁₁ sp₁₁ => ?_
  have r6₁₁ : s₁₁.gpr .r6 = Kb s₀ := by
    rw [g₁₁ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r6₁₀]
  refine dbl_wp r6₁₁ (by decide) (by decide) (by omega) (by omega)
    (by rw [rd₁₁, wr₁₁, rdwr₁₀]; exact cKr 0 16 (by decide)) (by rw [wr₁₁, wr₁₀]; exact cK 16 16 (by decide))
    fun s₁₂ g₁₂ m₁₂ rd₁₂ wr₁₂ sp₁₂ => ?_
  have k₁₂ : ∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r4 → r ≠ .r12 → s₁₂.gpr r = s₁₀.gpr r :=
    fun r h0 h1 h2 h3 h4 h12 => by rw [g₁₂ r h0 h1 h2 h3 h4 h12, g₁₁ r h0 h1 h2 h3 h4 h12]
  have r5₁₂ : s₁₂.gpr .r5 = Sc s₀ := by
    rw [k₁₂ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      sv .r5 (by simp [preserved]) (by decide), r5₉]
  have rdwr₁₂ : s₁₂.rd ++ s₁₂.wr = s₀.rd ++ s₀.wr := by rw [rd₁₂, wr₁₂, rd₁₁, wr₁₁, rdwr₁₀]
  have inS : ∀ d, d + 4 ≤ 2176 → InRegions (s₁₂.rd ++ s₁₂.wr) (State.addr (Sc s₀) + BitVec.ofNat 64 d) 4 :=
    fun d hd => by
      rw [rdwr₁₂]
      exact rw' (cS d 4 hd) ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩
  refine restoreB_ok [(.r4, 2064), (.r6, 2072), (.lr, 2076)] s₁₂ _ (by decide) (fun p hp' => ?_)
    fun s₁₃ ld₁₃ ho₁₃ m₁₃ rd₁₃ wr₁₃ sp₁₃ => ?_
  · have hb : 2064 ≤ p.2 ∧ p.2 + 4 ≤ 2080 ∧ p.1 ≠ .r5 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp'
      rcases hp' with rfl | rfl | rfl <;> decide
    exact ⟨hb.2.2, by omega, by rw [r5₁₂]; omega, by rw [r5₁₂]; exact inS _ (by omega)⟩
  refine wp_ldr (a := State.addr (Sc s₀) + BitVec.ofNat 64 2068) (by decide)
    (by rw [ho₁₃ _ (by decide), r5₁₂]; exact aS (by decide))
    (by rw [rd₁₃, wr₁₃]; exact inS _ (by decide)) fun s₁₄ u₁₄ => WP.block_nil ?_
  -- The slots.
  have slotD : ∀ d, 2064 ≤ d → d + 4 ≤ 2080 →
      ∀ r ∈ [⟨State.addr (Sc s₀ + BitVec.ofNat 32 2048), 16⟩, ⟨State.addr (Kb s₀), 16⟩,
        ⟨State.addr (Sc s₀), 2048⟩, below s₉], (⟨State.addr (Sc s₀) + BitVec.ofNat 64 d, 4⟩ : Region).Disjoint r := by
    intro d h₁ h₂ r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [cA]; exact Offset.disjoint _ (by omega) (by omega) (by omega)
    · exact (hp.k_scr.symm.sub_left (Offset.sub_base _ (by omega))).sub_right (Region.sub_prefix (by decide))
    · exact Offset.disjoint_base _ (by omega) (by omega)
    · rw [hb]; exact hp.b_scr.symm.sub_left (Offset.sub_base _ (by omega))
  have slotK : ∀ d, 2064 ≤ d → d + 4 ≤ 2080 → ∀ e, e ≤ 16 →
      (⟨State.addr (Sc s₀) + BitVec.ofNat 64 d, 4⟩ : Region).Disjoint ⟨State.addr (Kb s₀) + BitVec.ofNat 64 e, 16⟩ :=
    fun d h₁ h₂ e he => (hp.k_scr.symm.sub_left (Offset.sub_base _ (by omega))).sub_right (Offset.sub_base _ (by omega))
  have slot : ∀ r d, (r, d) ∈ saved4 → s₁₂.mem.readW (State.addr (Sc s₀) + BitVec.ofNat 64 d) 32 = s₀.gpr r := by
    intro r d hrd
    have hd : 2064 ≤ d ∧ d + 4 ≤ 2080 := by
      simp only [saved4, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hrd
      omega
    rw [m₁₂, dblMem_frame _ _ _ _ |>.readW (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact slotK d hd.1 hd.2 16 (by decide)) (by decide),
      m₁₁, dblMem_frame _ _ _ _ |>.readW (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact slotK d hd.1 hd.2 0 (by decide)) (by decide),
      h₁₀.frame.readW (Region.contains_self _ _) (slotD d hd.1 hd.2) (by decide), mem₉, preMem,
      Proof.Cmac.zero4, Proof.Cmac.readW_store4_of_sep _ _ _ _
        ((hp.k_scr.sub_left (Region.sub_prefix (by decide))).sub_right (Offset.sub_base _ (by omega))),
      Proof.Cmac.zero4, Proof.Cmac.readW_store4_of_sep _ _ _ _ (Offset.disjoint _ (by omega) (by omega) (by omega)),
      saved4_slot _ _ _ hrd]
  refine ⟨⟨fun r hr => ?_, by rw [u₁₄.sp, sp₁₃, sp₁₂, sp₁₁, h₁₀.sp, sp₉]⟩, ?_⟩
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [u₁₄.other _ (by decide), ld₁₃ (.r4, 2064) (by simp), r5₁₂, slot .r4 2064 (by decide)]
    · rw [u₁₄.gpr, m₁₃, slot .r5 2068 (by decide)]
    · rw [u₁₄.other _ (by decide), ld₁₃ (.r6, 2072) (by simp), r5₁₂, slot .r6 2072 (by decide)]
    all_goals first
      | rw [u₁₄.other _ (by decide), ld₁₃ (.lr, 2076) (by simp), r5₁₂, slot .lr 2076 (by decide)]
      | rw [u₁₄.other _ (by decide), ho₁₃ _ (by decide),
          k₁₂ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
          sv _ (by simp [preserved]) (by decide),
          keep₉ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
  · show Spec.Aes.bytesAt s₁₄.mem (State.addr (Kb s₀)) 32 = _
    have b₁₁ : Spec.Aes.bytesAt s₁₁.mem (State.addr (Kb s₀)) 16 =
        Spec.Cmac.dbl 16 (Spec.Aes.bytesAt s₁₀.mem (State.addr (Kb s₀)) 16) := by
      have := dblMem_bytes s₁₀.mem (State.addr (Kb s₀)) 0 0
      rw [add0] at this; rw [m₁₁, this]
    have lo : Spec.Aes.bytesAt s₁₂.mem (State.addr (Kb s₀)) 16 = Spec.Aes.bytesAt s₁₁.mem (State.addr (Kb s₀)) 16 := by
      rw [m₁₂]
      exact Proof.Cmac.bytesAt_frame16 (dblMem_frame _ _ _ _) fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (Offset.disjoint_base _ (by decide) (by omega)).symm
    have hi : Spec.Aes.bytesAt s₁₂.mem (State.addr (Kb s₀) + BitVec.ofNat 64 16) 16 =
        Spec.Cmac.dbl 16 (Spec.Aes.bytesAt s₁₁.mem (State.addr (Kb s₀)) 16) := by
      have := dblMem_bytes s₁₁.mem (State.addr (Kb s₀)) 0 16
      rw [add0] at this; rw [m₁₂, this]
    rw [u₁₄.mem, m₁₃, Proof.Cmac.bytesAt_32, lo, hi, b₁₁, L]
    rfl

end VG.Proof.CmacAes.Arm
