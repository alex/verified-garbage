import VerifiedGarbage.Proof.CmacAes.Stream.Arm.Common
import VerifiedGarbage.Proof.Framework.Arm.ArgTaint

/-!
# Streaming AES-CMAC on ARMv7: `vg_cmac_aes_init`

The code saves `r4`–`r6` and `lr` in the scratch buffer, expands the key into
the state, derives the subkeys after the schedule, zeroes the chaining value
and restores the registers: the state then represents the empty message. The
code between the calls is constant time by the taint analysis, and the calls
by their own proofs (`ek_rel`, `sub_rel`), their arguments pinned by `IMid₁`
and `IMid₂`.
-/

namespace VG.Proof.CmacAes.Stream.Arm

open VG VG.Arm VG.Impl.CmacAes.Stream.Arm
open VG.Impl.CmacAes.Arm (mov)
open VG.Proof.MdStream.Arm (Upd Mupd Fupd op2_imm op2_reg op2_lsr wp_mov wp_add wp_ldr wp_str saveMem
  saveList_ok saveMem_frame readW_writeW_save)
open VG.Proof.CmacAes.Arm (zeroBlk zeroBlk_ok)

/-- The precondition, by name: the state `St`, the key `Kp` of `KL` bytes
and the scratch buffer `S`. -/
structure IPre (s₀ : State) (St Kp S : BitVec 32) (KL : Nat) : Prop where
  r0 : s₀.gpr .r0 = St
  r1 : s₀.gpr .r1 = Kp
  r2 : (s₀.gpr .r2).toNat = KL
  r3 : s₀.gpr .r3 = S
  rd : s₀.rd = [⟨State.addr Kp, KL⟩]
  wr : s₀.wr = [⟨State.addr St, 304⟩, ⟨State.addr S, 2304⟩]
  st_k : (⟨State.addr St, 304⟩ : Region).Disjoint ⟨State.addr Kp, KL⟩
  st_s : (⟨State.addr St, 304⟩ : Region).Disjoint ⟨State.addr S, 2304⟩
  k_s : (⟨State.addr Kp, KL⟩ : Region).Disjoint ⟨State.addr S, 2304⟩
  b_st : (blw8 s₀).Disjoint ⟨State.addr St, 304⟩
  b_k : (blw8 s₀).Disjoint ⟨State.addr Kp, KL⟩
  b_s : (blw8 s₀).Disjoint ⟨State.addr S, 2304⟩
  fSt : St.toNat + 304 ≤ 2 ^ 32
  fK : Kp.toNat + KL ≤ 2 ^ 32
  fS : S.toNat + 2304 ≤ 2 ^ 32
  sp : 8 ≤ s₀.sp.toNat
  klen : KL = 16 ∨ KL = 24 ∨ KL = 32

theorem IPre.of {s₀ : State} (h : initArm.pre s₀) :
    IPre s₀ (s₀.gpr .r0) (s₀.gpr .r1) (s₀.gpr .r3) (s₀.gpr .r2).toNat :=
  let ⟨a, b, c, d, e, f, g, i, j, k, l, m, n⟩ := h
  ⟨rfl, rfl, rfl, rfl, a, b, c, d, e, f, g, i, j, k, l, m, n⟩

/-- The registers saved, and where. -/
def isaved : List (Reg × Nat) := [(.r4, 2176), (.r5, 2180), (.r6, 2184), (.lr, 2188)]

theorem isaved_bound : ∀ p ∈ isaved, 2176 ≤ p.2 ∧ p.2 + 4 ≤ 2192 := by decide

theorem initPre_eq : initPre = isaved.map (fun p => Instr.str p.1 .r3 p.2) ++
    [mov .r4 .r0, mov .r5 .r3, .mov .r6 (.shifted .r2 .lsr 2), .dp .add .r6 .r6 (.imm 6), mov .r0 .r1,
      mov .r1 .r2, mov .r2 .r4] := rfl

/-- The memory after saving the registers. -/
def iMem (s₀ : State) (S : BitVec 32) : Mem := saveMem s₀.mem (State.addr S) s₀.gpr isaved

theorem iMem_slot (s₀ : State) (S : BitVec 32) {r : Reg} {d : Nat} (h : (r, d) ∈ isaved) :
    (iMem s₀ S).readW (State.addr S + BitVec.ofNat 64 d) 32 = s₀.gpr r :=
  Spill.saveMem_saved (lo := 2176) (hi := 2192) (State.addr S) s₀.gpr s₀.mem isaved (by decide) (r, d) h

theorem iMem_frame (s₀ : State) (S : BitVec 32) : Frame [⟨State.addr S, 2304⟩] s₀.mem (iMem s₀ S) :=
  Spill.saveMem_frame _ _ _ (by decide) isaved (by decide)

/-- The rounds, as `lsr 2; add 6` computes them from the key length. -/
theorem rounds_bv {KL : Nat} (h : KL = 16 ∨ KL = 24 ∨ KL = 32) :
    BitVec.ofNat 32 KL >>> 2 + 6 = BitVec.ofNat 32 (KL / 4 + 6) := by
  rcases h with rfl | rfl | rfl <;> decide

theorem IPre.rounds {s₀ : State} {St Kp S : BitVec 32} {KL : Nat} (hp : IPre s₀ St Kp S KL) :
    KL / 4 + 6 = 10 ∨ KL / 4 + 6 = 12 ∨ KL / 4 + 6 = 14 := by
  rcases hp.klen with h | h | h <;> subst h <;> decide

/-! ## Before the first call -/

/-- What the code before the first call leaves. -/
structure IMid₁ (s₀ : State) (St Kp S : BitVec 32) (KL : Nat) (s : State) : Prop where
  args : EArgs s Kp St S KL
  r4 : s.gpr .r4 = St
  r5 : s.gpr .r5 = S
  r6 : s.gpr .r6 = BitVec.ofNat 32 (KL / 4 + 6)
  sp : s.sp = s₀.sp
  keep : ∀ r ∈ preserved, r ≠ .r4 → r ≠ .r5 → r ≠ .r6 → s.gpr r = s₀.gpr r
  mem : s.mem = iMem s₀ S
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem initPre_wp {s₀ : State} {St Kp S : BitVec 32} {KL : Nat} (hp : IPre s₀ St Kp S KL) :
    WP isa (.block initPre) s₀ (IMid₁ s₀ St Kp S KL) := by
  have hS := hp.fS
  have hSt := hp.fSt
  rw [initPre_eq]
  refine saveList_ok isaved s₀ _ (fun p hp' => ?_) fun s₁ g₁ rd₁ wr₁ sp₁ m₁ => ?_
  · have := isaved_bound p hp'
    rw [hp.r3, hp.wr]
    exact ⟨by omega, by omega, ⟨⟨State.addr S, 2304⟩, by simp, Offset.contains_base _ (by omega) (by omega)⟩⟩
  refine wp_mov (op2_reg _ _) fun s₂ u₂ => wp_mov (op2_reg _ _) fun s₃ u₃ =>
    wp_mov (op2_lsr (by decide)) fun s₄ u₄ => wp_add (op2_imm (by decide)) fun s₅ u₅ =>
    wp_mov (op2_reg _ _) fun s₆ u₆ => wp_mov (op2_reg _ _) fun s₇ u₇ => wp_mov (op2_reg _ _) fun s₈ u₈ =>
    WP.block_nil ?_
  have hKL : s₀.gpr .r2 = BitVec.ofNat 32 KL :=
    BitVec.eq_of_toNat_eq (by rw [hp.r2, toNat_ofNat32 (by rcases hp.klen with h | h | h <;> omega)])
  have rd₈ : s₈.rd = s₀.rd := by rw [u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, rd₁]
  have wr₈ : s₈.wr = s₀.wr := by rw [u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, wr₁]
  have r4 : s₈.gpr .r4 = St := by
    simp (disch := decide) only [u₈.other, u₇.other, u₆.other, u₅.other, u₄.other, u₃.other, u₂.gpr, g₁, hp.r0]
  have r5 : s₈.gpr .r5 = S := by
    simp (disch := decide) only [u₈.other, u₇.other, u₆.other, u₅.other, u₄.other, u₃.gpr, u₂.other, g₁, hp.r3]
  refine ⟨?_, r4, r5, ?_, by rw [u₈.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, sp₁], fun r hr h4 h5 h6 => ?_,
    by rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, m₁, hp.r3]; rfl, rd₈, wr₈⟩
  · refine
    { r0 := by simp (disch := decide) only [u₈.other, u₇.other, u₆.gpr, u₅.other, u₄.other, u₃.other, u₂.other,
          g₁, hp.r1]
      r1 := by simp (disch := decide) only [u₈.other, u₇.gpr, u₆.other, u₅.other, u₄.other, u₃.other, u₂.other,
          g₁, hKL]
      r2 := by rw [u₈.gpr, ← r4, u₈.other _ (by decide)]
      r3 := by simp (disch := decide) only [u₈.other, u₇.other, u₆.other, u₅.other, u₄.other, u₃.other, u₂.other,
          g₁, hp.r3]
      klen := hp.klen
      kw := hp.st_k.symm.sub_right (Region.sub_prefix (by decide))
      ks := hp.k_s.sub_right (Region.sub_prefix (by decide))
      ws := (hp.st_s.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide))
      fK := hp.fK, fW := by omega, fS := by omega
      reads := by
        rw [rd₈, wr₈, hp.rd, hp.wr]
        exact Covers.of_sub fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact ⟨⟨State.addr Kp, KL⟩, by simp, 0, (BitVec.add_zero _).symm, by simp⟩
      writes := by
        rw [wr₈, hp.wr]
        refine Covers.of_sub fun r hr => ?_
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact ⟨⟨State.addr St, 304⟩, by simp, 0, (BitVec.add_zero _).symm, by simp⟩
        · exact ⟨⟨State.addr S, 2304⟩, by simp, 0, (BitVec.add_zero _).symm, by simp⟩ }
  · simp (disch := decide) only [u₈.other, u₇.other, u₆.other, u₅.gpr, u₄.gpr, u₃.other, u₂.other, g₁, hKL]
    exact rounds_bv hp.klen
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl h4
    | exact absurd rfl h5
    | exact absurd rfl h6
    | simp (disch := decide) only [u₈.other, u₇.other, u₆.other, u₅.other, u₄.other, u₃.other, u₂.other, g₁]

/-! ## Between the calls -/

/-- What the call of `vg_aes_expand_key` leaves, for `initMid`. -/
structure IAfter (s₀ : State) (St S : BitVec 32) (KL : Nat) (s : State) : Prop where
  r4 : s.gpr .r4 = St
  r5 : s.gpr .r5 = S
  r6 : s.gpr .r6 = BitVec.ofNat 32 (KL / 4 + 6)
  sp : s.sp = s₀.sp
  keep : ∀ r ∈ preserved, r ≠ .r4 → r ≠ .r5 → r ≠ .r6 → r ≠ .lr → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem ek_after {s₀ s : State} {St Kp S : BitVec 32} {KL : Nat} (h : IMid₁ s₀ St Kp S KL s) :
    WP isa (.call "vg_aes_expand_key" Impl.Aes.Arm.expandKey) s (IAfter s₀ St S KL) :=
  WP.mono (ek_call h.args) fun _ h₂ =>
    ⟨by rw [h₂.saved _ (by simp [preserved]) (by decide), h.r4],
      by rw [h₂.saved _ (by simp [preserved]) (by decide), h.r5],
      by rw [h₂.saved _ (by simp [preserved]) (by decide), h.r6], by rw [h₂.sp, h.sp],
      fun r hr a b c d => by rw [h₂.saved r hr d, h.keep r hr a b c], by rw [h₂.rd, h.rd], by rw [h₂.wr, h.wr]⟩

/-- The subkeys, after the schedule. -/
abbrev Kof (St : BitVec 32) : BitVec 32 := St + BitVec.ofNat 32 240

/-- What the code between the calls leaves. -/
structure IMid₂ (s₀ : State) (St S : BitVec 32) (KL : Nat) (m : Mem) (s : State) : Prop where
  args : SArgs s St (Kof St) S (KL / 4 + 6)
  mem : s.mem = m
  r4 : s.gpr .r4 = St
  r5 : s.gpr .r5 = S
  sp : s.sp = s₀.sp
  keep : ∀ r ∈ preserved, r ≠ .r4 → r ≠ .r5 → r ≠ .r6 → r ≠ .lr → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem IPre.aK {s₀ : State} {St Kp S : BitVec 32} {KL : Nat} (hp : IPre s₀ St Kp S KL) :
    State.addr (Kof St) = State.addr St + BitVec.ofNat 64 240 := addr_add (by have := hp.fSt; omega)

theorem initMid_wp {s₀ s : State} {St Kp S : BitVec 32} {KL : Nat} (hp : IPre s₀ St Kp S KL)
    (h : IAfter s₀ St S KL s) : WP isa (.block initMid) s (IMid₂ s₀ St S KL s.mem) := by
  have hSt := hp.fSt
  have hS := hp.fS
  refine wp_mov (op2_reg _ _) fun s₁ u₁ => wp_mov (op2_reg _ _) fun s₂ u₂ => wp_add (op2_imm (by decide))
    fun s₃ u₃ => wp_mov (op2_reg _ _) fun s₄ u₄ => WP.block_nil ?_
  have rd₄ : s₄.rd = s₀.rd := by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd, h.rd]
  have wr₄ : s₄.wr = s₀.wr := by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr]
  have sp₄ : s₄.sp = s₀.sp := by rw [u₄.sp, u₃.sp, u₂.sp, u₁.sp, h.sp]
  have kSt : Region.Sub ⟨State.addr (Kof St), 32⟩ ⟨State.addr St, 304⟩ := by
    rw [hp.aK]; exact Offset.sub_base _ (by decide)
  refine ⟨?_, by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem],
    by simp (disch := decide) only [u₄.other, u₃.other, u₂.other, u₁.other, h.r4],
    by simp (disch := decide) only [u₄.other, u₃.other, u₂.other, u₁.other, h.r5], sp₄,
    fun r hr a b c d => ?_, rd₄, wr₄⟩
  · exact
    { r0 := by simp (disch := decide) only [u₄.other, u₃.other, u₂.other, u₁.gpr, h.r4]
      r1 := by simp (disch := decide) only [u₄.other, u₃.other, u₂.gpr, u₁.other, h.r6]
      r2 := by simp (disch := decide) only [u₄.other, u₃.gpr, u₂.other, u₁.other, h.r4]; rfl
      r3 := by simp (disch := decide) only [u₄.gpr, u₃.other, u₂.other, u₁.other, h.r5]
      rounds := hp.rounds
      hsp := by rw [sp₄]; exact hp.sp
      wk := by rw [hp.aK]; exact Offset.base_disjoint _ (by decide) (by omega)
      ws := (hp.st_s.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide))
      ks := (hp.st_s.sub_left kSt).sub_right (Region.sub_prefix (by decide))
      bw := by rw [blw8, sp₄]; exact hp.b_st.sub_right (Region.sub_prefix (by decide))
      bk := by rw [blw8, sp₄]; exact hp.b_st.sub_right kSt
      bs := by rw [blw8, sp₄]; exact hp.b_s.sub_right (Region.sub_prefix (by decide))
      fW := by omega
      fK := by rw [toNat_add_ofNat (by omega)]; omega
      fS := by omega
      reads := by
        rw [rd₄, wr₄, hp.rd, hp.wr]
        exact Covers.of_sub fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact ⟨⟨State.addr St, 304⟩, by simp, 0, (BitVec.add_zero _).symm, by simp⟩
      writes := by
        rw [wr₄, hp.wr]
        refine Covers.of_sub fun r hr => ?_
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact ⟨⟨State.addr St, 304⟩, by simp, 240, hp.aK, by simp⟩
        · exact ⟨⟨State.addr S, 2304⟩, by simp, 0, (BitVec.add_zero _).symm, by simp⟩ }
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl a
    | exact absurd rfl b
    | exact absurd rfl c
    | exact absurd rfl d
    | (simp (disch := decide) only [u₄.other, u₃.other, u₂.other, u₁.other]
       exact h.keep _ (by simp [preserved]) (by decide) (by decide) (by decide) (by decide))

/-! ## After the calls -/

theorem initPost_eq : initPost = .mov .r12 (.imm 0) :: (zeroBlk .r12 .r4 272 ++
    ([(.r4, 2176), (.r6, 2184), (.lr, 2188)] : List (Reg × Nat)).map (fun p => Instr.ldr p.1 .r5 p.2) ++
    ([.ldr .r5 .r5 2180] : List Instr)) := rfl

/-- The memory after zeroing the chaining value. -/
abbrev zcv (m : Mem) (St : BitVec 32) : Mem := Proof.Cmac.zero4 m (State.addr St + BitVec.ofNat 64 272)

theorem initPost_wp {s : State} {St S : BitVec 32} (hSt : St.toNat + 304 ≤ 2 ^ 32) (hS : S.toNat + 2304 ≤ 2 ^ 32)
    (h4 : s.gpr .r4 = St) (h5 : s.gpr .r5 = S)
    (w : Covers [⟨State.addr St + BitVec.ofNat 64 272, 16⟩] s.wr)
    (r : ∀ d, 2176 ≤ d → d + 4 ≤ 2192 → InRegions (s.rd ++ s.wr) (State.addr S + BitVec.ofNat 64 d) 4) :
    WP isa (.block initPost) s fun s' =>
      s'.gpr .r4 = (zcv s.mem St).readW (State.addr S + BitVec.ofNat 64 2176) 32 ∧
      s'.gpr .r5 = (zcv s.mem St).readW (State.addr S + BitVec.ofNat 64 2180) 32 ∧
      s'.gpr .r6 = (zcv s.mem St).readW (State.addr S + BitVec.ofNat 64 2184) 32 ∧
      s'.gpr .lr = (zcv s.mem St).readW (State.addr S + BitVec.ofNat 64 2188) 32 ∧
      (∀ x, x ≠ .r4 → x ≠ .r5 → x ≠ .r6 → x ≠ .lr → x ≠ .r12 → s'.gpr x = s.gpr x) ∧
      s'.sp = s.sp ∧ s'.mem = zcv s.mem St := by
  rw [initPost_eq]
  refine wp_mov (op2_imm (by decide)) fun s₁ u₁ => ?_
  refine zeroBlk_ok (by rw [u₁.gpr]) (by decide) (by rw [u₁.other _ (by decide), h4]; omega)
    (by rw [u₁.wr, u₁.other _ (by decide), h4]; exact w) fun s₂ g₂ m₂ rd₂ wr₂ sp₂ => ?_
  have e5 : s₂.gpr .r5 = S := by rw [g₂, u₁.other _ (by decide), h5]
  have mm : s₂.mem = zcv s.mem St := by rw [m₂, u₁.mem, u₁.other _ (by decide), h4]
  refine Spill.restoreList_ok [(.r4, 2176), (.r6, 2184), (.lr, 2188)] s₂ _ (by decide) (fun p hp' => ?_) fun s₃ ld₃ ho₃ m₃ rd₃ wr₃ sp₃ => ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp'
    rw [e5, rd₂, wr₂, u₁.rd, u₁.wr]
    rcases hp' with rfl | rfl | rfl
    · exact ⟨by decide, by decide, by omega, r _ (by decide) (by decide)⟩
    · exact ⟨by decide, by decide, by omega, r _ (by decide) (by decide)⟩
    · exact ⟨by decide, by decide, by omega, r _ (by decide) (by decide)⟩
  refine wp_ldr (a := State.addr S + BitVec.ofNat 64 2180) (by decide)
    (by rw [ho₃ _ (by decide), e5]; exact addr_add (by omega))
    (by rw [rd₃, wr₃, rd₂, wr₂, u₁.rd, u₁.wr]; exact r _ (by decide) (by decide)) fun s₄ u₄ => WP.block_nil ?_
  refine ⟨?_, ?_, ?_, ?_, fun x a b c d e => ?_, by rw [u₄.sp, sp₃, sp₂, u₁.sp], by rw [u₄.mem, m₃, mm]⟩
  · rw [u₄.other _ (by decide), ld₃ (.r4, 2176) (by simp), e5, mm]
  · rw [u₄.gpr, m₃, mm]
  · rw [u₄.other _ (by decide), ld₃ (.r6, 2184) (by simp), e5, mm]
  · rw [u₄.other _ (by decide), ld₃ (.lr, 2188) (by simp), e5, mm]
  · rw [u₄.other _ b, ho₃ _ (by simp [a, c, d]), g₂, u₁.other _ e]

/-! ## The whole function -/

theorem init_wp {s₀ : State} (h0 : initArm.pre s₀) :
    WP isa init s₀ fun s' => abiPreserved s₀ s' ∧ initArm.post s₀ s' := by
  have hp := IPre.of h0
  generalize s₀.gpr .r0 = St at hp
  generalize s₀.gpr .r1 = Kp at hp
  generalize s₀.gpr .r3 = S at hp
  generalize (s₀.gpr .r2).toNat = KL at hp
  have hSt := hp.fSt
  have hS := hp.fS
  have hR := hp.rounds
  refine WP.seq (WP.mono (initPre_wp hp) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (ek_call h₁.args) fun s₂ h₂ => ?_)
  have a₂ : IAfter s₀ St S KL s₂ :=
    ⟨by rw [h₂.saved _ (by simp [preserved]) (by decide), h₁.r4],
      by rw [h₂.saved _ (by simp [preserved]) (by decide), h₁.r5],
      by rw [h₂.saved _ (by simp [preserved]) (by decide), h₁.r6], by rw [h₂.sp, h₁.sp],
      fun r hr a b c d => by rw [h₂.saved r hr d, h₁.keep r hr a b c], by rw [h₂.rd, h₁.rd], by rw [h₂.wr, h₁.wr]⟩
  refine WP.seq (WP.mono (initMid_wp hp a₂) fun s₃ h₃ => ?_)
  refine WP.seq (WP.mono (sub_call h₃.args) fun s₄ h₄ => ?_)
  have rdwr₄ : s₄.rd ++ s₄.wr = [⟨State.addr Kp, KL⟩, ⟨State.addr St, 304⟩, ⟨State.addr S, 2304⟩] := by
    rw [h₄.rd, h₄.wr, h₃.rd, h₃.wr, hp.rd, hp.wr]; rfl
  refine WP.mono (initPost_wp (s := s₄) hSt hS
    (by rw [h₄.saved _ (by simp [preserved]) (by decide), h₃.r4])
    (by rw [h₄.saved _ (by simp [preserved]) (by decide), h₃.r5])
    (by
      rw [h₄.wr, h₃.wr, hp.wr]
      exact Covers.of_sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨⟨State.addr St, 304⟩, by simp, 272, rfl, by simp⟩)
    (fun d _ hd => by
      rw [rdwr₄]; exact ⟨⟨State.addr S, 2304⟩, by simp, Offset.contains_base _ (by omega) (by omega)⟩))
    fun s₅ ⟨r4₅, r5₅, r6₅, lr₅, g₅, sp₅, m₅⟩ => ?_
  -- The memory, step by step.
  have f₁ : Frame [⟨State.addr S, 2304⟩] s₀.mem s₁.mem := by rw [h₁.mem]; exact iMem_frame _ _
  have f₂ := h₂.frame
  have f₄ := h₄.frame
  have fz : Frame [⟨State.addr St + BitVec.ofNat 64 272, 16⟩] s₄.mem s₅.mem := by
    rw [m₅]; exact Proof.Cmac.frame_store4 _ _ _ _ _
  have m₃ : s₃.mem = s₂.mem := h₃.mem
  have sp₃ : s₃.sp = s₀.sp := h₃.sp
  have aK := hp.aK
  -- The saved registers.
  have slot (d : Nat) (hd : 2176 ≤ d) (hd' : d + 4 ≤ 2192) :
      (zcv s₄.mem St).readW (State.addr S + BitVec.ofNat 64 d) 32 = (iMem s₀ S).readW (State.addr S + BitVec.ofNat 64 d) 32 := by
    have sub : Region.Sub ⟨State.addr S + BitVec.ofNat 64 d, 4⟩ ⟨State.addr S, 2304⟩ := Offset.sub_base _ (by omega)
    have c := Region.contains_self (State.addr S + BitVec.ofNat 64 d) 4
    rw [← m₅, fz.readW c (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (hp.st_s.sub_left (Offset.sub_base _ (by decide))).symm.sub_left sub) (by decide),
      f₄.readW c (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [aK]; exact (hp.st_s.sub_left (Offset.sub_base _ (by decide))).symm.sub_left sub
        · exact Offset.disjoint_base _ hd (by omega)
        · rw [blw8, sp₃]; exact (hp.b_s.sub_right sub).symm) (by decide), m₃,
      f₂.readW c (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact (hp.st_s.sub_left (Region.sub_prefix (by decide))).symm.sub_left sub
        · exact Offset.disjoint_base _ (by omega) (by omega)) (by decide), h₁.mem]
  have keep₄ : ∀ x ∈ preserved, x ≠ .r4 → x ≠ .r5 → x ≠ .r6 → x ≠ .lr → s₄.gpr x = s₀.gpr x :=
    fun x hx a b c d => by rw [h₄.saved x hx d, h₃.keep x hx a b c d]
  refine ⟨⟨fun r hr => ?_, by rw [sp₅, h₄.sp, sp₃]⟩, ?_⟩
  · have hr' := hr
    simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [r4₅, slot 2176 (by decide) (by decide), iMem_slot s₀ S (r := .r4) (d := 2176) (by decide)]
    · rw [r5₅, slot 2180 (by decide) (by decide), iMem_slot s₀ S (r := .r5) (d := 2180) (by decide)]
    · rw [r6₅, slot 2184 (by decide) (by decide), iMem_slot s₀ S (r := .r6) (d := 2184) (by decide)]
    all_goals first
      | rw [lr₅, slot 2188 (by decide) (by decide), iMem_slot s₀ S (r := .lr) (d := 2188) (by decide)]
      | rw [g₅ _ (by decide) (by decide) (by decide) (by decide) (by decide),
          keep₄ _ hr' (by decide) (by decide) (by decide) (by decide)]
  · show Spec.Cmac.Repr s₅.mem (State.addr (s₀.gpr .r0))
      (Spec.Aes.bytesAt s₀.mem (State.addr (s₀.gpr .r1)) (s₀.gpr .r2).toNat) []
    rw [hp.r0, hp.r1, hp.r2, Proof.Cmac.Stream.repr_iff]
    have hkey : Spec.Aes.bytesAt s₁.mem (State.addr Kp) KL = Spec.Aes.bytesAt s₀.mem (State.addr Kp) KL :=
      Proof.Cmac.bytesAt_frame f₁ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hp.k_s) (by have := hp.fK; omega)
    have hlen : (Spec.Aes.bytesAt s₀.mem (State.addr Kp) KL).length = KL := Proof.Cmac.bytesAt_length _ _ _
    have hRb : 16 * (Spec.Aes.rounds (KL / 4) + 1) ≤ 240 := by simp only [Spec.Aes.rounds]; omega
    -- The schedule, from the first call on.
    have sch : Spec.Aes.bytesAt s₅.mem (State.addr St) (16 * (Spec.Aes.rounds (KL / 4) + 1)) =
        Spec.Aes.bytesAt s₂.mem (State.addr St) (16 * (Spec.Aes.rounds (KL / 4) + 1)) := by
      have sub : Region.Sub ⟨State.addr St, 16 * (Spec.Aes.rounds (KL / 4) + 1)⟩ ⟨State.addr St, 304⟩ :=
        Region.sub_prefix (by omega)
      rw [Proof.Cmac.bytesAt_frame fz (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact Offset.base_disjoint _ (by omega) (by decide))
          (by omega),
        Proof.Cmac.bytesAt_frame f₄ (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · rw [aK]; exact Offset.base_disjoint _ (by omega) (by decide)
          · exact (hp.st_s.sub_left sub).sub_right (Region.sub_prefix (by decide))
          · rw [blw8, sp₃]; exact (hp.b_st.sub_right sub).symm) (by omega), m₃]
    have hsch : Spec.Aes.bytesAt s₂.mem (State.addr St) (16 * (Spec.Aes.rounds (KL / 4) + 1)) =
        Spec.Aes.expandKey (Spec.Aes.bytesAt s₀.mem (State.addr Kp) KL) := by rw [h₂.out, hkey]
    refine ⟨⟨by rw [hlen]; exact hp.klen, by rw [hlen, sch, hsch], ?_⟩, ?_, ?_⟩
    · show Spec.Aes.bytesAt s₅.mem (State.addr St + BitVec.ofNat 64 240) 32 = _
      rw [Proof.Cmac.bytesAt_frame fz (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint _ (by omega) (by omega) (by omega))
          (by decide), ← aK, h₄.out, m₃, show KL / 4 + 6 = Spec.Aes.rounds (KL / 4) from rfl, hsch]
      simp only [Spec.Cmac.aes, hlen]
    · show Spec.Aes.bytesAt s₅.mem (State.addr St + BitVec.ofNat 64 272) 16 = _
      rw [m₅]; exact Proof.Cmac.zero4_bytes _ _
    · simp [Proof.Cmac.Stream.held_zero, Spec.Aes.bytesAt]

/-! ## Constant time -/

theorem init_rel {s₀ s₀' : State} (h0 : initArm.pre s₀) (h0' : initArm.pre s₀') (hq : initArm.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') init fun _ _ => True := by
  obtain ⟨q1, q2, q3, q4, q5⟩ := hq
  have hp := IPre.of h0
  have hp' : IPre s₀' (s₀.gpr .r0) (s₀.gpr .r1) (s₀.gpr .r3) (s₀.gpr .r2).toNat := by
    rw [q2, q3, q4, q5]; exact IPre.of h0'
  generalize s₀.gpr .r0 = St at hp hp'
  generalize s₀.gpr .r1 = Kp at hp hp'
  generalize s₀.gpr .r3 = S at hp hp'
  generalize (s₀.gpr .r2).toNat = KL at hp hp'
  obtain ⟨_, hA⟩ : ∃ h, (taint.check (Taint.ofRegs [.r0, .r1, .r2, .r3]) (.block initPre) h).isSome = true :=
    ⟨_, by taint_decide⟩
  obtain ⟨_, hB⟩ : ∃ h, (taint.check (Taint.ofRegs [.r4, .r5, .r6]) (.block initMid) h).isSome = true :=
    ⟨_, by taint_decide⟩
  obtain ⟨_, hC⟩ : ∃ h, (taint.check (Taint.ofRegs [.r4, .r5]) (.block initPost) h).isSome = true :=
    ⟨_, by taint_decide⟩
  have a := rel_agree (F := fun s => s = s₀) (F' := fun s => s = s₀') (G := IMid₁ s₀ St Kp S KL)
    (G' := IMid₁ s₀' St Kp S KL) (Taint.ofRegs [.r0, .r1, .r2, .r3])
    (fun s s' e e' => by
      subst e e'
      refine Taint.agree_ofRegs fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> assumption) ⟨_, hA⟩
    (fun s e => by rw [e]; exact initPre_wp hp) (fun s e => by rw [e]; exact initPre_wp hp')
  have e := rel_wp (F := IMid₁ s₀ St Kp S KL) (F' := IMid₁ s₀' St Kp S KL) (G := IAfter s₀ St S KL)
    (G' := IAfter s₀' St S KL) (ek_rel fun _ _ h => ⟨h.1.args, h.2.args⟩) (fun _ h => ek_after h)
    (fun _ h => ek_after h)
  have m := rel_agree (F := IAfter s₀ St S KL) (F' := IAfter s₀' St S KL)
    (G := fun s => ∃ m, IMid₂ s₀ St S KL m s) (G' := fun s => ∃ m, IMid₂ s₀' St S KL m s)
    (Taint.ofRegs [.r4, .r5, .r6])
    (fun s s' h h' => by
      refine Taint.agree_ofRegs fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [h.r4, h'.r4]
      · rw [h.r5, h'.r5]
      · rw [h.r6, h'.r6]) ⟨_, hB⟩
    (fun s h => WP.mono (initMid_wp hp h) fun _ h => ⟨_, h⟩)
    (fun s h => WP.mono (initMid_wp hp' h) fun _ h => ⟨_, h⟩)
  have sk := rel_wp (F := fun s => ∃ m, IMid₂ s₀ St S KL m s) (F' := fun s => ∃ m, IMid₂ s₀' St S KL m s)
    (G := fun s => s.gpr .r4 = St ∧ s.gpr .r5 = S) (G' := fun s => s.gpr .r4 = St ∧ s.gpr .r5 = S)
    (sub_rel (sp₀ := s₀.sp) fun _ _ ⟨⟨_, h₁⟩, ⟨_, h₂⟩⟩ => ⟨h₁.args, h₂.args, h₁.sp, h₂.sp.trans q1.symm⟩)
    (fun _ ⟨_, h⟩ => WP.mono (sub_call h.args) fun _ h' =>
      ⟨by rw [h'.saved _ (by simp [preserved]) (by decide), h.r4],
        by rw [h'.saved _ (by simp [preserved]) (by decide), h.r5]⟩)
    (fun _ ⟨_, h⟩ => WP.mono (sub_call h.args) fun _ h' =>
      ⟨by rw [h'.saved _ (by simp [preserved]) (by decide), h.r4],
        by rw [h'.saved _ (by simp [preserved]) (by decide), h.r5]⟩)
  have p := RelCT.taint (A := taint)
    (P := fun a b => (a.gpr .r4 = St ∧ a.gpr .r5 = S) ∧ b.gpr .r4 = St ∧ b.gpr .r5 = S)
    (Taint.ofRegs [.r4, .r5]) (fun a b h => by
      refine Taint.agree_ofRegs fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h.1.1, h.2.1]
      · rw [h.1.2, h.2.2]) hC
  exact a.seq (e.seq (m.seq (sk.seq p)))

theorem init_ct : ConstantTime isa initArm.pre initArm.pub init :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (init_rel h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.CmacAes.Stream.Arm
