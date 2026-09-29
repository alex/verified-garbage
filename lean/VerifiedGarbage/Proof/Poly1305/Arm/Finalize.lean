import VerifiedGarbage.Proof.Poly1305.Arm.Steps
import VerifiedGarbage.Proof.Poly1305.Arm.Contract
import VerifiedGarbage.Proof.Framework.Arm.Taint

/-!
# Poly1305 on 32-bit ARM: `finalize`

Untrusted: everything here is checked by Lean. After saving the registers in
`scratch` (`prologue_ok`), a non-empty buffer is padded in place with `0x01`
and zeros (`pad_ok`); its length is stored, the limbs of `r` computed and
the accumulator loaded (`mid_ok`); the padded buffer is absorbed
(`last_ok`); then the columns are reduced fully, `s` is added, and the sum is
carried and stored modulo `2¹²⁸` in `out` (`tag_ok`). Until then (`FC`),
only the state's working space, the buffer, the accumulator and `scratch`
change.
-/

namespace VG.Proof.Poly1305.Arm.Fin

open VG VG.Arm VG.Impl.Poly1305.Arm VG.Proof.Poly1305.Arm
open VG.Spec.Poly1305 (P clamp leNum bytesAt accumulate Repr Buffered leBytes mac)

/-! ## The precondition -/

section
variable (s₀ : State)
/-- `out` and `scratch`. -/
abbrev oP : BitVec 32 := stackArg s₀ 0
abbrev oA : Addr := State.addr (oP s₀)
abbrev oR : Region := ⟨oA s₀, 16⟩
abbrev sc : BitVec 32 := stackArg s₀ 1
/-- The stack arguments. -/
abbrev argR : Region := ⟨stackArgAddr s₀ 0, 8⟩
/-- The number of bytes buffered, and the bytes. -/
abbrev kb : Nat := (s₀.gpr .r2).toNat % 16
abbrev Bf : List Byte := bytesAt s₀.mem (stB s₀ + 56) (kb s₀)
end

structure FPre (s₀ : State) : Prop where
  rd : s₀.rd = [argR s₀]
  wr : s₀.wr = [stR (s₀.gpr .r0), oR s₀, scrR (sc s₀)]
  st_o : (stR (s₀.gpr .r0)).Disjoint (oR s₀)
  st_scr : (stR (s₀.gpr .r0)).Disjoint (scrR (sc s₀))
  o_scr : (oR s₀).Disjoint (scrR (sc s₀))
  a_st : (argR s₀).Disjoint (stR (s₀.gpr .r0))
  a_o : (argR s₀).Disjoint (oR s₀)
  a_scr : (argR s₀).Disjoint (scrR (sc s₀))
  st_fit : (s₀.gpr .r0).toNat + 128 ≤ 2 ^ 32
  o_fit : (oP s₀).toNat + 16 ≤ 2 ^ 32
  sc_fit : (sc s₀).toNat + 128 ≤ 2 ^ 32
  sp_fit : s₀.sp.toNat + 8 ≤ 2 ^ 32

theorem FPre.of (s : State) (h : Proof.Poly1305.finalizeArm.pre s) : FPre s := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩

theorem kb_lt (s₀ : State) : kb s₀ < 16 := Nat.mod_lt _ (by omega)

theorem FPre.stW {s₀ : State} (hp : FPre s₀) {s : State} (h : s.wr = s₀.wr) : stR (s₀.gpr .r0) ∈ s.wr := by
  rw [h, hp.wr]; exact List.mem_cons_self

theorem FPre.oW {s₀ : State} (hp : FPre s₀) {s : State} (h : s.wr = s₀.wr) : oR s₀ ∈ s.wr := by
  rw [h, hp.wr]; exact List.mem_cons_of_mem _ List.mem_cons_self

theorem FPre.scW {s₀ : State} (hp : FPre s₀) {s : State} (h : s.wr = s₀.wr) : scrR (sc s₀) ∈ s.wr := by
  rw [h, hp.wr]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))

/-- A range of the state is disjoint from `scratch`. -/
theorem FPre.st_scr' {s₀ : State} (hp : FPre s₀) {a n : Nat} (h : a + n ≤ 128) :
    (⟨stB s₀ + BitVec.ofNat 64 a, n⟩ : Region).Disjoint (scrR (sc s₀)) :=
  hp.st_scr.sub_left (sub_base _ h (by omega))

/-! ## What holds until the tag is stored -/

/-- The state's working space and buffer (`wkL`) and `scratch`. -/
abbrev fF (s₀ : State) : List Region := offR (stB s₀) wkL ++ [scrR (sc s₀)]

structure FC (s₀ s : State) : Prop where
  r0 : s.gpr .r0 = s₀.gpr .r0
  lr : s.gpr .lr = s₀.gpr .lr
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : Frame (fF s₀) s₀.mem s.mem
  saved : SavedS (State.addr (sc s₀)) s₀.gpr s.mem

theorem FC.keepsF {s₀ : State} (hp : FPre s₀) {s s' : State} (h : FC s₀ s) {ws : List Reg}
    {l : List (Nat × Nat)} (hk : KeepsF ws (offR (stB s₀) l) s s') (hws : Reg.r0 ∉ ws ∧ Reg.lr ∉ ws)
    (hl : (l.all fun p => wkL.any fun q => q.1 ≤ p.1 ∧ p.1 + p.2 ≤ q.1 + q.2) = true)
    (hl' : (l.all fun p => p.1 + p.2 ≤ 128) = true) : FC s₀ s' where
  r0 := by rw [hk.gpr _ hws.1, h.r0]
  lr := by rw [hk.gpr _ hws.2, h.lr]
  rd := hk.rd.trans h.rd
  wr := hk.wr.trans h.wr
  sp := hk.sp.trans h.sp
  frame := h.frame.trans ((hk.frame.offR_sub hl (by decide)).mono fun _ hr => List.mem_append_left _ hr)
  saved := fun i hi => by
    rw [hk.frame.readW (Region.contains_self _ _) (fun r hr => by
      obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hr
      have := List.all_eq_true.mp hl' p hp'
      simp only [decide_eq_true_eq] at this
      exact ((hp.st_scr' this).symm.sub_left (sub_base _ (by omega) (by omega)))) (by decide)]
    exact h.saved i hi

theorem FC.upd {s₀ s s' : State} (h : FC s₀ s) {d : Reg} {v : BitVec 32} (u : Upd s s' d v)
    (hd : d ≠ .r0 ∧ d ≠ .lr) : FC s₀ s' :=
  ⟨by rw [u.other _ (Ne.symm hd.1), h.r0], by rw [u.other _ (Ne.symm hd.2), h.lr], u.rd.trans h.rd,
    u.wr.trans h.wr, u.sp.trans h.sp, by rw [u.mem]; exact h.frame, by rw [u.mem]; exact h.saved⟩

theorem FC.flags {s₀ s s' : State} (h : FC s₀ s) (u : Fupd s s') : FC s₀ s' :=
  ⟨by rw [u.gpr, h.r0], by rw [u.gpr, h.lr], u.rd.trans h.rd, u.wr.trans h.wr, u.sp.trans h.sp,
    by rw [u.mem]; exact h.frame, by rw [u.mem]; exact h.saved⟩

theorem FC.keeps {s₀ s s' : State} (h : FC s₀ s) {ws : List Reg} (k : Keeps ws s s')
    (hws : Reg.r0 ∉ ws ∧ Reg.lr ∉ ws) : FC s₀ s' :=
  ⟨by rw [k.gpr _ hws.1, h.r0], by rw [k.gpr _ hws.2, h.lr], k.rd.trans h.rd, k.wr.trans h.wr, k.sp.trans h.sp,
    by rw [k.mem]; exact h.frame, by rw [k.mem]; exact h.saved⟩

/-- The address of stack argument `i`. -/
theorem argAddr {s₀ : State} (hp : FPre s₀) {i : Nat} (hi : i < 2) :
    stackArgAddr s₀ i = stackArgAddr s₀ 0 + BitVec.ofNat 64 (4 * i) := by
  have := hp.sp_fit
  simp only [stackArgAddr]
  rw [addr_add (by omega), addr_add (by omega)]
  simp

/-- Loading stack argument `i`, whose memory is as on entry. -/
theorem wp_arg {s₀ : State} (hp : FPre s₀) {s : State} (hsp : s.sp = s₀.sp) (hrd : s.rd = s₀.rd) {i : Nat}
    (hi : i < 2) (hm : s.mem.readW (stackArgAddr s₀ i) 32 = stackArg s₀ i) {t : Reg}
    {is : List Instr} {Q : State → Prop}
    (k : ∀ s', Upd s s' t (stackArg s₀ i) → WP isa (.block is) s' Q) :
    WP isa (.block (.ldrSp t (4 * i) :: is)) s Q := by
  have := hp.sp_fit
  refine wp_ldrSp (a := stackArgAddr s₀ i) (by omega) (by rw [hsp]; rfl)
    (by rw [hrd, hp.rd, argAddr hp hi]
        exact ⟨_, List.mem_append_left _ (List.mem_singleton_self _), contains_off (by omega) (by omega)⟩)
    fun s' u => ?_
  rw [hm] at u
  exact k s' u

/-- The stack arguments are unchanged by writes to the state, `out` and `scratch`. -/
theorem FPre.arg {s₀ : State} (hp : FPre s₀) {m : Mem}
    (hf : Frame (offR (stB s₀) wkL ++ [oR s₀, scrR (sc s₀)]) s₀.mem m) {i : Nat} (hi : i < 2) :
    m.readW (stackArgAddr s₀ i) 32 = stackArg s₀ i := by
  rw [stackArg, hf.readW (r := argR s₀) (by rw [argAddr hp hi]; exact contains_off (by omega) (by omega))
    (fun r hr => ?_) (by decide)]
  rcases List.mem_append.mp hr with hr | hr
  · obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hr
    simp only [wkL, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl <;> exact hp.a_st.sub_right (sub_base _ (by omega) (by omega))
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.a_o
    · exact hp.a_scr

theorem FC.frame' {s₀ s : State} (h : FC s₀ s) :
    Frame (offR (stB s₀) wkL ++ [oR s₀, scrR (sc s₀)]) s₀.mem s.mem :=
  h.frame.mono fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · exact List.mem_append_left _ hr
    · simp only [List.mem_singleton] at hr; subst hr
      exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))

/-! ## Prologue -/

theorem sub0 (x : BitVec 32) : x - 0 = x := by simp

theorem and15 (x : BitVec 32) : x &&& (15 : BitVec 32) = BitVec.ofNat 32 (x.toNat % 16) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (15 : BitVec 32).toNat = 2 ^ 4 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := x.toNat % 16) (by omega)]

/-- After the prologue. -/
structure P1 (s₀ s : State) : Prop extends FC s₀ s where
  sfr : Frame [scrR (sc s₀)] s₀.mem s.mem
  r4 : s.gpr .r4 = BitVec.ofNat 32 (kb s₀)
  z : s.z = decide (kb s₀ = 0)

theorem prologue_ok {s₀ : State} (hp : FPre s₀) :
    WP isa (.block ([.ldrSp .r12 4] ++ saveScr ++ [.dp .and .r4 .r2 (.imm 15), .cmp .r4 (.imm 0)])) s₀
      (P1 s₀) := by
  have hsc := hp.sc_fit
  refine wp_arg (i := 1) hp rfl rfl (by omega) rfl fun s₁ u₁ => ?_
  refine WP.append (saveScr_ok hsc u₁.gpr (by rw [u₁.wr]; exact hp.scW rfl))
    fun s₂ ⟨hsv, hf₂, hg₂, hrd₂, hwr₂, hsp₂⟩ => ?_
  have hf₂' : Frame [scrR (sc s₀)] s₀.mem s₂.mem := by
    rw [← u₁.mem]; exact hf₂.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by omega)⟩
  have fc₂ : FC s₀ s₂ :=
    ⟨by rw [hg₂, u₁.other _ (by decide)], by rw [hg₂, u₁.other _ (by decide)], by rw [hrd₂, u₁.rd],
      by rw [hwr₂, u₁.wr], by rw [hsp₂, u₁.sp], hf₂'.mono fun _ hr => List.mem_append_right _ hr,
      fun i hi => by rw [hsv i hi, u₁.other _ (by revert i; decide)]⟩
  refine wp_and (op2_imm (by decide)) fun s₃ u₃ => ?_
  refine wp_cmp (op2_imm (by decide)) fun s₄ u₄ hz => WP.block_nil ?_
  have hr4 : s₃.gpr .r4 = BitVec.ofNat 32 (kb s₀) := by
    rw [u₃.gpr, hg₂, u₁.other _ (by decide)]
    exact and15 _
  refine ⟨(fc₂.upd u₃ (by decide)).flags u₄, by rw [u₄.mem, u₃.mem]; exact hf₂', by rw [u₄.gpr, hr4], ?_⟩
  rw [hz, hr4, sub0, ofNat_beq_zero (by have := kb_lt s₀; omega)]

/-! ## Padding the buffer in place -/

/-- Bytes `0`–`15` of the buffer of the state at `B` are `f 0`, …, `f 15`. -/
def BufHas (m : Mem) (B : Addr) (f : Nat → Byte) : Prop := ∀ k < 16, m (B + BitVec.ofNat 64 (56 + k)) = f k

/-- The padded block: the buffered bytes, `0x01`, zeros. -/
def padded (s₀ : State) (k : Nat) : Byte :=
  if k < kb s₀ then (Bf s₀).getD k 0 else if k = kb s₀ then 1 else 0

theorem buf_ne (B : Addr) {j k : Nat} (hj : j < 16) (hk : k < 16) (h : k ≠ j) :
    B + BitVec.ofNat 64 (56 + k) ≠ B + BitVec.ofNat 64 (56 + j) := by
  intro he
  have h2 : BitVec.ofNat 64 (56 + k) = BitVec.ofNat 64 (56 + j) := by simpa using he
  have := congrArg BitVec.toNat h2
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
  exact h (by omega)

/-- The zero loop's invariant, before byte `j`, from the state `s₁` after the prologue. -/
structure ZInv (s₀ s₁ : State) (j : Nat) (s : State) : Prop where
  j_le : kb s₀ ≤ j ∧ j ≤ 16
  r1 : s.gpr .r1 = s₀.gpr .r0 + BitVec.ofNat 32 j
  r5 : s.gpr .r5 = BitVec.ofNat 32 (16 - j)
  r12 : s.gpr .r12 = 0
  keeps : KeepsF [.r1, .r5, .r12] (offR (stB s₀) [(56, 16)]) s₁ s
  buf : BufHas s.mem (stB s₀) fun k => if k < j then (if k < kb s₀ then s₁.mem (stB s₀ + BitVec.ofNat 64 (56 + k))
    else 0) else s₁.mem (stB s₀ + BitVec.ofNat 64 (56 + k))

theorem zinit_ok {s₀ s₁ : State} (h₁ : P1 s₀ s₁) :
    WP isa (.block [.mov .r12 (.imm 0), .dp .add .r1 .r0 (.reg .r4), .mov .r5 (.imm 16),
      .dp .sub .r5 .r5 (.reg .r4)]) s₁ (ZInv s₀ s₁ (kb s₀)) := by
  have hk := kb_lt s₀
  refine wp_mov (op2_imm (by decide)) fun s₂ u₂ => wp_add (op2_reg _ _) fun s₃ u₃ =>
    wp_mov (op2_imm (by decide)) fun s₄ u₄ => wp_sub (op2_reg _ _) fun s₅ u₅ => WP.block_nil ?_
  refine ⟨⟨le_rfl, hk.le⟩, ?_, ?_, ?_, ⟨fun r hr => ?_, ?_, ?_, ?_, ?_⟩, fun k hk' => ?_⟩
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.other .r0 (by decide),
      u₂.other .r4 (by decide), h₁.r0, h₁.r4]
  · rw [u₅.gpr, u₄.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), h₁.r4,
      show (16 : BitVec 32) = BitVec.ofNat 32 16 from rfl]
    conv_lhs => rw [show 16 = (16 - kb s₀) + kb s₀ by omega, BitVec.ofNat_add]
    rw [BitVec.add_sub_cancel]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u₅.other _ hr.2.1, u₄.other _ hr.2.1, u₃.other _ hr.1, u₂.other _ hr.2.2]
  · rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem]; exact Frame.refl _ _
  · rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd]
  · rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr]
  · rw [u₅.sp, u₄.sp, u₃.sp, u₂.sp]
  · rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem]
    by_cases h : k < kb s₀ <;> simp [h]

theorem zero_step {s₀ : State} (hp : FPre s₀) {s₁ : State} (h₁ : P1 s₀ s₁) {j : Nat} (hj : j < 16) {s : State}
    (h : ZInv s₀ s₁ j s) :
    WP isa (.block [.strb .r12 .r1 56, .dp .add .r1 .r1 (.imm 1), .subs .r5 .r5 (.imm 1)]) s fun s' =>
      ZInv s₀ s₁ (j + 1) s' ∧ s'.z = decide (16 - (j + 1) = 0) := by
  have hfit := hp.st_fit
  refine wp_strb (t := .r12) (a := stB s₀ + BitVec.ofNat 64 (56 + j)) (by decide)
    (by rw [h.r1, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_comm j]; exact ea hfit (by omega))
    (by rw [h.keeps.wr]; exact outSt (hp.stW h₁.wr) (by omega)) fun s₂ m₂ => ?_
  refine wp_add (op2_imm (by decide)) fun s₃ u₃ => wp_subs (op2_imm (by decide)) fun s₄ u₄ hz => WP.block_nil ?_
  have hr5 : s₄.gpr .r5 = BitVec.ofNat 32 (16 - (j + 1)) := by
    rw [u₄.gpr, u₃.other _ (by decide), m₂.gpr, h.r5, show 16 - j = (16 - (j + 1)) + 1 by omega,
      BitVec.ofNat_add]
    exact BitVec.add_sub_cancel _ _
  refine ⟨⟨⟨h.j_le.1.trans (Nat.le_succ _), by omega⟩, ?_, hr5, ?_, ⟨fun r hr => ?_, ?_, ?_, ?_, ?_⟩,
    fun k hk => ?_⟩, ?_⟩
  · rw [u₄.other _ (by decide), u₃.gpr, m₂.gpr, h.r1, add_ofNat_one]
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), m₂.gpr, h.r12]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u₄.other _ hr.2.1, u₃.other _ hr.1, m₂.gpr, h.keeps.gpr r (by simp [hr.1, hr.2.1, hr.2.2])]
  · rw [u₄.mem, u₃.mem, m₂.mem]
    exact Frame.writeOff h.keeps.frame (a := 56) (len := 16) (List.mem_singleton_self _) (by omega) (by omega)
      (by omega) _ rfl
  · rw [u₄.rd, u₃.rd, m₂.rd, h.keeps.rd]
  · rw [u₄.wr, u₃.wr, m₂.wr, h.keeps.wr]
  · rw [u₄.sp, u₃.sp, m₂.sp, h.keeps.sp]
  · rw [u₄.mem, u₃.mem, m₂.mem, writeW8_apply]
    by_cases hkj : k = j
    · subst hkj
      rw [iteT rfl, h.r12]
      simp only [show k < k + 1 by omega, ite_true, show ¬ k < kb s₀ by have := h.j_le.1; omega, ite_false]
      rfl
    · rw [iteF (buf_ne _ hj hk hkj), h.buf k hk]
      by_cases h1 : k < j
      · simp only [h1, ite_true, show k < j + 1 by omega]
      · simp only [h1, ite_false, show ¬ k < j + 1 by omega]
  · rw [hz, ← u₄.gpr, hr5, ofNat_beq_zero (by omega)]

theorem pad1_ok {s₀ : State} (hp : FPre s₀) {s₁ : State} (h₁ : P1 s₀ s₁) {s : State} (h : ZInv s₀ s₁ 16 s) :
    WP isa (.block [.mov .r12 (.imm 1), .dp .add .r1 .r0 (.reg .r4), .strb .r12 .r1 56]) s fun s' =>
      KeepsF [.r1, .r5, .r12] (offR (stB s₀) [(56, 16)]) s₁ s' ∧ BufHas s'.mem (stB s₀) (padded s₀) := by
  have hfit := hp.st_fit
  have hk := kb_lt s₀
  refine wp_mov (op2_imm (by decide)) fun s₂ u₂ => wp_add (op2_reg _ _) fun s₃ u₃ => ?_
  have hr1 : s₃.gpr .r1 = s₀.gpr .r0 + BitVec.ofNat 32 (kb s₀) := by
    rw [u₃.gpr, u₂.other .r0 (by decide), u₂.other .r4 (by decide), h.keeps.gpr .r0 (by decide),
      h.keeps.gpr .r4 (by decide), h₁.r0, h₁.r4]
  refine wp_strb (t := .r12) (a := stB s₀ + BitVec.ofNat 64 (56 + kb s₀)) (by decide)
    (by rw [hr1, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_comm (kb s₀)]; exact ea hfit (by omega))
    (by rw [u₃.wr, u₂.wr, h.keeps.wr]; exact outSt (hp.stW h₁.wr) (by omega)) fun s₄ m₄ =>
      WP.block_nil ⟨⟨fun r hr => ?_, ?_, ?_, ?_, ?_⟩, fun k hk' => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [m₄.gpr, u₃.other _ hr.1, u₂.other _ hr.2.2, h.keeps.gpr r (by simp [hr.1, hr.2.1, hr.2.2])]
  · rw [m₄.mem, u₃.mem, u₂.mem]
    exact Frame.writeOff h.keeps.frame (a := 56) (len := 16) (List.mem_singleton_self _) (by omega) (by omega)
      (by omega) _ rfl
  · rw [m₄.rd, u₃.rd, u₂.rd, h.keeps.rd]
  · rw [m₄.wr, u₃.wr, u₂.wr, h.keeps.wr]
  · rw [m₄.sp, u₃.sp, u₂.sp, h.keeps.sp]
  · have hB : ∀ k < kb s₀, s₁.mem (stB s₀ + BitVec.ofNat 64 (56 + k)) = (Bf s₀).getD k 0 := fun k hk'' => by
      simp only [Bf, bytesAt, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk'',
        Option.map_some, Option.getD_some]
      rw [show (56 : Addr) = BitVec.ofNat 64 56 from rfl, off_add]
      refine h₁.sfr _ fun r hr hc => ?_
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.st_scr' (a := 56 + k) (n := 1) (by omega) _ (Region.contains_self _ _) hc
    rw [m₄.mem, u₃.mem, u₂.mem, writeW8_apply, u₃.other _ (by decide), u₂.gpr]
    by_cases hkj : k = kb s₀
    · subst hkj
      rw [iteT rfl]
      simp only [padded, Nat.lt_irrefl, ite_false, ite_true]
      rfl
    · rw [iteF (buf_ne _ hk hk' hkj), h.buf k hk']
      simp only [hk', ite_true]
      by_cases h1 : k < kb s₀
      · simp only [h1, ite_true, padded, hB k h1]
      · simp only [h1, ite_false, padded, hkj]

theorem padBuf_ok {s₀ : State} (hp : FPre s₀) {s₁ : State} (h₁ : P1 s₀ s₁) :
    WP isa padBuf s₁ fun s =>
      KeepsF [.r1, .r5, .r12] (offR (stB s₀) [(56, 16)]) s₁ s ∧ BufHas s.mem (stB s₀) (padded s₀) := by
  have hkl := kb_lt s₀
  refine WP.seq (WP.mono (zinit_ok h₁) fun s₂ h₂ => ?_)
  refine WP.seq (WP.mono (Q := ZInv s₀ s₁ 16) ?_ fun s₃ h₃ => pad1_ok hp h₁ h₃)
  refine WP.loop (M := isa) (fun n s => ∃ j, n = 16 - j ∧ j < 16 ∧ ZInv s₀ s₁ j s) ?_ _ s₂
    ⟨kb s₀, rfl, hkl, h₂⟩
  rintro n s ⟨j, rfl, hj, hz⟩
  refine WP.mono (zero_step hp h₁ hj hz) fun s' ⟨h', hz'⟩ => ?_
  by_cases hl : j + 1 = 16
  · exact .inl ⟨by rw [eval_ne, hz']; simp [hl], hl ▸ h'⟩
  · exact .inr ⟨by rw [eval_ne, hz']; simp; omega, _, by omega, j + 1, rfl, by omega, h'⟩

/-- The padded block as a number: the buffered bytes with `0x01` appended. -/
theorem padded_value {s₀ : State} {m : Mem} (h : BufHas m (stB s₀) (padded s₀)) :
    leNum (bytesAt m (stB s₀ + BitVec.ofNat 64 56) 16) = leNum (Bf s₀ ++ [0x01]) := by
  have hk := kb_lt s₀
  have hlen : (Bf s₀).length = kb s₀ := Poly1305.length_bytesAt _ _ _
  have hl : bytesAt m (stB s₀ + BitVec.ofNat 64 56) 16 = (Bf s₀ ++ [0x01]) ++ List.replicate (15 - kb s₀) 0 := by
    apply List.ext_getElem
    · simp [hlen, Poly1305.length_bytesAt]; omega
    · intro k h₁ h₂
      rw [Poly1305.length_bytesAt] at h₁
      have e : (bytesAt m (stB s₀ + BitVec.ofNat 64 56) 16)[k] = padded s₀ k := by
        simp only [bytesAt, List.getElem_map, List.getElem_range]
        rw [off_add]; exact h k h₁
      refine e.trans ?_
      rcases Nat.lt_trichotomy k (kb s₀) with hk' | rfl | hk'
      · rw [List.getElem_append_left (by simp [hlen]; omega), List.getElem_append_left (by omega)]
        simp only [padded, hk', ite_true]
        simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show k < (Bf s₀).length by omega)]
      · rw [List.getElem_append_left (by simp [hlen]), List.getElem_append_right (by omega)]
        simp [padded, hlen]
      · rw [List.getElem_append_right (by simp [hlen]; omega)]
        simp [padded, show ¬ k < kb s₀ by omega, show k ≠ kb s₀ by omega]
  rw [hl, Poly1305.leNum_append _ (List.replicate _ _), Poly1305.leNum_replicate_zero, Nat.mul_zero, Nat.add_zero]

/-- After padding the buffer. -/
structure F2 (s₀ s : State) : Prop extends FC s₀ s where
  sfr : Frame (offR (stB s₀) [(56, 16)] ++ [scrR (sc s₀)]) s₀.mem s.mem
  r4 : s.gpr .r4 = BitVec.ofNat 32 (kb s₀)
  buf : 0 < kb s₀ → BufHas s.mem (stB s₀) (padded s₀)

theorem pad_ok {s₀ : State} (hp : FPre s₀) {s : State} (h : P1 s₀ s) :
    WP isa (.ite .eq (.block []) padBuf) s (F2 s₀) := by
  refine WP.ite s.z (eval_eq _) (fun hb => WP.block_nil ?_) (fun hb => ?_)
  · have hk : kb s₀ = 0 := by rw [h.z] at hb; simpa using hb
    exact ⟨h.toFC, h.sfr.mono fun _ hr => List.mem_append_right _ hr, h.r4, fun hk' => absurd hk (by omega)⟩
  · refine WP.mono (padBuf_ok hp h) fun s' ⟨k', hb'⟩ => ⟨h.toFC.keepsF hp k' (by decide) (by decide)
      (by decide), ?_, by rw [k'.gpr _ (by decide), h.r4], fun _ => hb'⟩
    exact (h.sfr.mono fun _ hr => List.mem_append_right _ hr).trans
      (k'.frame.mono fun _ hr => List.mem_append_left _ hr)

/-! ## The limbs of `r` and the accumulator -/

/-- A word of the state outside the buffer, after padding it. -/
theorem sfr_word {s₀ : State} (hp : FPre s₀) {m : Mem}
    (hf : Frame (offR (stB s₀) [(56, 16)] ++ [scrR (sc s₀)]) s₀.mem m) {d : Nat}
    (hd : d + 4 ≤ 56 ∨ 72 ≤ d ∧ d + 4 ≤ 128) :
    m.readW (stB s₀ + BitVec.ofNat 64 d) 32 = s₀.mem.readW (stB s₀ + BitVec.ofNat 64 d) 32 :=
  hf.readW (Region.contains_self _ _) (fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · simp only [offR, List.map_cons, List.map_nil, List.mem_singleton] at hr; subst hr
      exact disjoint_sub _ (by omega) (by omega) (by omega)
    · simp only [List.mem_singleton] at hr; subst hr
      exact hp.st_scr' (by omega)) (by decide)

/-- After computing the limbs of `r` and loading the accumulator. -/
structure F3 (s₀ s : State) : Prop extends FC s₀ s where
  acc : Acc (s₀.gpr .r0) (Rl s₀) (A0 s₀) [] s
  buf : 0 < kb s₀ → BufHas s.mem (stB s₀) (padded s₀)
  z : s.z = decide (kb s₀ = 0)

theorem BufHas.frame {s₀ : State} {m m' : Mem} (h : BufHas m (stB s₀) (padded s₀)) {l : List (Nat × Nat)}
    (hf : Frame (offR (stB s₀) l) m m') (hl : (l.all fun p => 72 ≤ p.1 ∨ p.1 + p.2 ≤ 56) = true)
    (hl' : (l.all fun p => p.1 + p.2 < 2 ^ 32) = true) : BufHas m' (stB s₀) (padded s₀) := fun k hk => by
  rw [← h k hk]
  refine hf _ fun r hr hc => ?_
  exact (dj_offR _ (d := 56) (n := 16) (by
    rw [List.all_eq_true] at hl ⊢
    intro p hp; have := hl p hp; simp only [decide_eq_true_eq] at this ⊢; omega) (by omega) hl' r hr) _
    (by rw [← off_add]; exact contains_off (by omega) (by omega)) hc

theorem mid_ok {s₀ : State} (hp : FPre s₀) {s : State} (h : F2 s₀ s) :
    WP isa (.block (.str .r4 .r0 ptrOff :: setupR ++ loadAcc ++ [.ldr .r1 .r0 ptrOff, .cmp .r1 (.imm 0)])) s
      (F3 s₀) := by
  have hfit := hp.st_fit
  have hk := kb_lt s₀
  have hw := hp.stW h.wr
  refine wp_str (a := stB s₀ + BitVec.ofNat 64 124) (by decide)
    (by rw [h.r0]; exact ea hfit (off := 124) (by omega)) (outSt hw (off := 124) (n := 4) (by omega))
    fun s₁ u₁ => ?_
  have f₁ : Frame (offR (stB s₀) [(124, 4)]) s.mem s₁.mem := by
    rw [u₁.mem]
    exact Frame.writeOff (Frame.refl _ _) (a := 124) (len := 4) (List.mem_singleton_self _) le_rfl le_rfl
      (by omega) _ rfl
  have fc₁ : FC s₀ s₁ := h.toFC.keepsF hp (ws := []) ⟨fun r _ => by rw [u₁.gpr], f₁, u₁.rd, u₁.wr, u₁.sp⟩
    (by decide) (by decide) (by decide)
  refine WP.append (setupAcc_ok hfit fc₁.r0 (hp.stW fc₁.wr)) fun s₂ ⟨hr₂, hc₂, k₂⟩ => ?_
  have fc₂ : FC s₀ s₂ := fc₁.keepsF hp k₂ (by decide) (by decide) (by decide)
  refine wp_ldr (a := stB s₀ + BitVec.ofNat 64 124) (by decide)
    (by rw [fc₂.r0]; exact ea hfit (off := 124) (by omega)) (inSt (hp.stW fc₂.wr) (off := 124) (n := 4) (by omega))
    fun s₃ u₃ => wp_cmp (op2_imm (by decide)) fun s₄ u₄ hz => WP.block_nil ?_
  have m₄ : s₄.mem = s₂.mem := by rw [u₄.mem, u₃.mem]
  have hw₁ : ∀ d, (d + 4 ≤ 56 ∨ 72 ≤ d ∧ d + 4 ≤ 124) →
      s₁.mem.readW (stB s₀ + BitVec.ofNat 64 d) 32 = s₀.mem.readW (stB s₀ + BitVec.ofNat 64 d) 32 := fun d hd => by
    rw [f₁.word (by simp only [List.all_cons, List.all_nil, Bool.and_true, decide_eq_true_eq]; omega) (by omega)
      (by decide)]
    exact sfr_word hp h.sfr (by omega)
  have hRl : rlimb s₁.mem (stB s₀) = Rl s₀ := rlimb_frame fun i hi => hw₁ _ (by omega)
  have hA : accD s₁.mem (stB s₀) = accD s₀.mem (stB s₀) := accD_of_words fun i hi => hw₁ _ (by omega)
  refine ⟨(fc₂.upd u₃ (by decide)).flags u₄, ⟨by rw [u₄.gpr, u₃.other _ (by decide), fc₂.r0],
    hp.stW (by rw [u₄.wr, u₃.wr, fc₂.wr]), fun k hk => ?_, accD s₀.mem (stB s₀), ⟨fun k hk => ?_, ?_⟩,
    fun k _ => by have := accD_lt s₀.mem (stB s₀) k; omega, by rw [Poly1305.absorbAll_nil]⟩, fun hpos => ?_, ?_⟩
  · rw [m₄, hr₂ k hk, hRl]
  · have := yr_ne k hk
    rw [u₄.gpr, u₃.other _ this.2.1, ← hA]; exact hc₂.1 k hk
  · rw [m₄, ← hA]; exact hc₂.2
  · rw [m₄]
    exact ((h.buf hpos).frame f₁ (by decide) (by decide)).frame k₂.frame (by decide) (by decide)
  · rw [hz, u₃.gpr, k₂.frame.word (by decide) (by decide) (by decide), u₁.mem, Mem.readW_writeW_self32, h.r4,
      sub0, ofNat_beq_zero (by omega)]

/-! ## The last block -/

/-- After absorbing the padded buffer, if any. -/
structure F4 (s₀ s : State) : Prop extends FC s₀ s where
  acc : Acc (s₀.gpr .r0) (Rl s₀) (A0 s₀) (Bf s₀) s

theorem last_ok {s₀ : State} (hp : FPre s₀) {s : State} (h : F3 s₀ s) :
    WP isa (.ite .eq (.block []) (.block (.dp .add .r1 .r0 (.imm 56) :: absorb false))) s (F4 s₀) := by
  have hfit := hp.st_fit
  have hk := kb_lt s₀
  refine WP.ite s.z (eval_eq _) (fun hb => WP.block_nil ?_) (fun hb => ?_)
  · have h0 : kb s₀ = 0 := by rw [h.z] at hb; simpa using hb
    refine ⟨h.toFC, ?_⟩
    have : Bf s₀ = [] := by simp [Bf, h0, bytesAt]
    rw [this]; exact h.acc
  · have hpos : 0 < kb s₀ := by rw [h.z] at hb; simp only [decide_eq_false_iff_not] at hb; omega
    refine wp_add (op2_imm (by decide)) fun s₁ u₁ => ?_
    obtain ⟨D, hcD, hDb, hDv⟩ := h.acc.acc
    have hr1 : s₁.gpr .r1 = s₀.gpr .r0 + 56 := by rw [u₁.gpr, h.r0]
    have ha : ∀ j < 4, State.addr (s₁.gpr .r1 + BitVec.ofNat 32 (4 * j)) =
        stB s₀ + BitVec.ofNat 64 56 + BitVec.ofNat 64 (4 * j) := fun j hj => by
      rw [hr1, BitVec.add_assoc, show (56 : BitVec 32) = BitVec.ofNat 32 56 from rfl, ← BitVec.ofNat_add,
        ea hfit (by omega), off_add]
    refine WP.mono (absorb_ok hfit false (R := Rl s₀) (D := D) (fun i _ => rlimb_lt _ _ i) hDb
      (by rw [u₁.other _ (by decide), h.r0]) (by rw [u₁.wr]; exact hp.stW h.wr)
      (fun k hk => by rw [u₁.mem]; exact h.acc.r k hk)
      ⟨fun k hk => by rw [u₁.other _ (yr_ne k hk).2.1]; exact hcD.1 k hk, by rw [u₁.mem]; exact hcD.2⟩
      (fun j hj => by rw [ha j hj, off_add, u₁.rd, u₁.wr]; exact inSt (hp.stW h.wr) (by omega)))
      fun s₂ ⟨D', hc₂, hb₂, hv₂, k₂⟩ => ?_
    have f₂ : Frame (offR (stB s₀) [(0, 20)]) s₁.mem s₂.mem := by rw [← accR_offR]; exact k₂.frame
    have k₂' : KeepsF work (offR (stB s₀) [(0, 20)]) s₁ s₂ := ⟨k₂.gpr, f₂, k₂.rd, k₂.wr, k₂.sp⟩
    have fc₂ := (h.toFC.upd u₁ (by decide)).keepsF hp k₂' (by decide) (by decide) (by decide)
    have hmsg : msgVal s₁ = leNum (Bf s₀ ++ [0x01]) := by
      rw [← padded_value (m := s₁.mem) (by rw [u₁.mem]; exact h.buf hpos), leNum_bytesAt_16]
      simp only [msgVal, word]
      rw [ha 0 (by omega), ha 1 (by omega), ha 2 (by omega), ha 3 (by omega)]
    have hl : (Bf s₀).length = kb s₀ := Poly1305.length_bytesAt _ _ _
    refine ⟨fc₂, fc₂.r0, hp.stW fc₂.wr, fun k hk => ?_, D', hc₂, hb₂, ?_⟩
    · rw [rval_frame k₂.frame hk, u₁.mem]; exact h.acc.r k hk
    · rw [hv₂, hmsg, Poly1305.absorbAll_block (by omega) (by omega), iteF (show ¬(false = true) by simp),
        Nat.add_zero]
      rw [Poly1305.absorbAll_nil] at hDv
      exact mod_step hDv

/-! ## The tag -/

/-- The tag's stores. -/
def tagList : List (Reg × Nat × Bool) := [(.r3, 0, false), (.r5, 4, false), (.r7, 8, false), (.r10, 12, false)]

/-- The sum of `h mod p` and `s`, carried. -/
def sumL (D : Nat → Nat) (w : Nat → Nat) : Nat → Nat := fun k => redL D k + mlimb (w 0) (w 1) (w 2) (w 3) k

theorem cnt_mod (s₀ : State) : (Proof.Poly1305.countArm s₀).toNat % 16 = kb s₀ := by
  simp only [kb, Proof.Poly1305.countArm]
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt (s₀.gpr .r2).isLt, Nat.shiftLeft_eq]
  omega

theorem tag_ok {s₀ : State} (hp : FPre s₀) {s : State} (h : F4 s₀ s) :
    WP isa (.block (reduce ++ [.str .r1 .r0 d9Off, .dp .add .r1 .r0 (.imm 40)] ++ addWords ++ addTop false ++
      mask :: (List.range 9).flatMap carryStep ++ toWords ++
      [.ldrSp .r2 0, .str .r3 .r2 0, .str .r5 .r2 4, .str .r7 .r2 8, .str .r10 .r2 12, .ldrSp .r12 4] ++
      restoreScr)) s fun s' => abiPreserved s₀ s' ∧ Proof.Poly1305.finalizeArm.post s₀ s' := by
  have hfit := hp.st_fit
  obtain ⟨D, hcD, hDb, hDv⟩ := h.acc.acc
  have hs0 : s.gpr .r0 = s₀.gpr .r0 := h.r0
  have hw : stR (s₀.gpr .r0) ∈ s.wr := hp.stW h.wr
  have hE : ∀ j < 10, D j < 2 ^ 32 - 2 ^ 19 := fun j hj => by have := hDb j hj; omega
  obtain ⟨-, -, -, hvL, hlL⟩ := red_facts D hE
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine WP.append (reduce_ok hfit hDb hs0 hw hcD) fun s₁ ⟨hc₁, k₁⟩ => ?_
  have hs₁0 : s₁.gpr .r0 = s₀.gpr .r0 := by rw [k₁.gpr _ (by decide), hs0]
  have hw₁ : stR (s₀.gpr .r0) ∈ s₁.wr := by rw [k₁.wr]; exact hw
  refine wp_str (a := stB s₀ + BitVec.ofNat 64 16) (by decide) (by rw [hs₁0]; exact ea hfit (off := 16) (by omega))
    (outSt hw₁ (off := 16) (n := 4) (by omega)) fun s₂ u₂ => ?_
  refine wp_add (op2_imm (by decide)) fun s₃ u₃ => ?_
  have hr1 : s₃.gpr .r1 = s₀.gpr .r0 + 40 := by rw [u₃.gpr, u₂.gpr, hs₁0]
  have hw₃ : stR (s₀.gpr .r0) ∈ s₃.wr := by rw [u₃.wr, u₂.wr]; exact hw₁
  have hsA : ∀ i < 4, State.addr (s₃.gpr .r1 + BitVec.ofNat 32 (4 * i)) = stB s₀ + BitVec.ofNat 64 (40 + 4 * i) :=
    fun i hi => by
      rw [hr1, BitVec.add_assoc, show (40 : BitVec 32) = BitVec.ofNat 32 40 from rfl, ← BitVec.ofNat_add]
      exact ea hfit (by omega)
  refine WP.append (addWords_ok fun i hi => by rw [hsA i hi]; exact inSt hw₃ (by omega)) fun s₄ ⟨hc₄, hr₄, k₄⟩ => ?_
  -- The words of `s`.
  let w : Nat → Nat := fun i => (s₀.mem.readW (stB s₀ + BitVec.ofNat 64 (40 + 4 * i)) 32).toNat
  have m₃ : s₃.mem = s₁.mem.writeW (stB s₀ + BitVec.ofNat 64 16) (s₁.gpr .r1) := by rw [u₃.mem, u₂.mem]
  have hf₀₃ : Frame (fF s₀) s₀.mem s₃.mem := by
    rw [m₃, k₁.mem]
    exact Frame.writeW h.frame (List.mem_append_left _ (List.mem_map.mpr ⟨(0, 24), by decide, rfl⟩)) _
      (contains_sub _ (by omega) (by omega) (by omega))
  have hword : ∀ i < 4, (word s₃ i).toNat = w i := fun i hi => by
    simp only [word, w]
    rw [hsA i hi, hf₀₃.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)]
    rcases List.mem_append.mp hr with hr | hr
    · exact (dj_offR _ (d := 24) (n := 32) (by decide) (by omega) (by decide) r hr).sub_left
        (sub_sub _ (by omega) (by omega) (by omega))
    · simp only [List.mem_singleton] at hr; subst hr
      exact hp.st_scr' (by omega)
  have hw4 : ∀ i, w i < 2 ^ 32 := fun i => BitVec.isLt _
  have hml := fun k => mlimb_lt (hw4 0) (hw4 1) (hw4 2) (hw4 3) k
  -- `addTop false`: the top column.
  simp only [addTop, Bool.false_eq_true, ite_false, List.append_nil, List.cons_append, List.nil_append]
  have hs₄0 : s₄.gpr .r0 = s₀.gpr .r0 := by rw [k₄.gpr _ (by decide), u₃.other _ (by decide), u₂.gpr, hs₁0]
  have hw₄ : stR (s₀.gpr .r0) ∈ s₄.wr := by rw [k₄.wr]; exact hw₃
  refine wp_ldr (a := stB s₀ + BitVec.ofNat 64 16) (by decide) (by rw [hs₄0]; exact ea hfit (off := 16) (by omega))
    (inSt hw₄ (off := 16) (n := 4) (by omega)) fun s₅ u₅ => wp_add (op2_lsr (by omega)) fun s₆ u₆ => ?_
  refine wp_movw fun s₇ u₇ => ?_
  have hL9 := hlL 9 (by omega)
  have hcols : Cols (sumL D w) s₇ := fun j hj => by
    rcases Nat.lt_or_ge j 9 with hj9 | hj9
    · have hne := yr_ne j hj9
      have e₁ := hc₁ j hj
      have := hlL j hj; have := hml j
      rw [u₇.other _ hne.2.2.1, u₆.other _ hne.2.1, u₅.other _ hne.2.1, hc₄ j hj9,
        u₃.other _ hne.2.1, u₂.gpr, toNat_add_lt (by rw [e₁, wsum_toNat _ hj9, hword 0 (by omega),
          hword 1 (by omega), hword 2 (by omega), hword 3 (by omega)]; omega), e₁, wsum_toNat _ hj9,
        hword 0 (by omega), hword 1 (by omega), hword 2 (by omega), hword 3 (by omega)]
      rfl
    · have e9 : (s₅.gpr .r1).toNat = redL D 9 := by
        rw [u₅.gpr, k₄.mem, m₃, Mem.readW_writeW_self32]; exact hc₁ 9 (by omega)
      have e2 : (s₅.gpr .r2).toNat = w 3 := by
        rw [u₅.other _ (by decide), hr₄, hword 3 (by omega)]
      have := hml 9
      rw [show j = 9 by omega, yr9, u₇.other _ (by decide), u₆.gpr, toNat_add_lt (by rw [e9, toNat_shr, e2]; omega),
        e9, toNat_shr, e2]
      rfl
  have hfb : ∀ j < 10, sumL D w j < 2 ^ 32 - 2 ^ 19 := fun j hj => by
    have := hlL j hj; have := hml j; simp only [sumL]; omega
  refine WP.append (carries_ok 0 9 (by omega) hfb hcols u₇.gpr) fun s₈ ⟨hc₈, k₈⟩ => ?_
  have hL : ∀ j < 9, carryN (sumL D w) 0 9 j < 2 ^ 13 := fun j hj => carryN_lt _ 0 9 j (by omega) (by omega)
  refine WP.append (toWords_ok hc₈ hL) fun s₉ ⟨e3, e5, e7, e10, _, k₉⟩ => ?_
  -- The stores into `out`.
  have m₉ : s₉.mem = s₃.mem := by
    rw [k₉.mem, k₈.mem, u₇.mem, u₆.mem, u₅.mem, k₄.mem]
  have g₉ : ∀ r, r ∉ [Reg.r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12] → s₉.gpr r = s.gpr r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hr
    rw [k₉.gpr _ (by simp [h1, h3, h5, h7, h10]), k₈.gpr _ (by simp [cregs, yregs, h1, h3, h4, h5, h6, h7, h8, h9,
      h10, h11]), u₇.other _ h2, u₆.other _ h1, u₅.other _ h1, k₄.gpr _ (by simp [yregs, h2, h12, h3, h4, h5, h6,
      h7, h8, h9, h10, h11]), u₃.other _ h1, u₂.gpr, k₁.gpr _ (by simp [cregs, yregs, h1, h2, h12, h3, h4, h5, h6,
      h7, h8, h9, h10, h11])]
  have hrd₉ : s₉.rd = s₀.rd := by
    rw [k₉.rd, k₈.rd, u₇.rd, u₆.rd, u₅.rd, k₄.rd, u₃.rd, u₂.rd, k₁.rd, h.rd]
  have hwr₉ : s₉.wr = s₀.wr := by
    rw [k₉.wr, k₈.wr, u₇.wr, u₆.wr, u₅.wr, k₄.wr, u₃.wr, u₂.wr, k₁.wr, h.wr]
  have hsp₉ : s₉.sp = s₀.sp := by
    rw [k₉.sp, k₈.sp, u₇.sp, u₆.sp, u₅.sp, k₄.sp, u₃.sp, u₂.sp, k₁.sp, h.sp]
  have F₃ : Frame (offR (stB s₀) wkL ++ [oR s₀, scrR (sc s₀)]) s₀.mem s₃.mem :=
    hf₀₃.mono fun r hr => by
      rcases List.mem_append.mp hr with hr | hr
      · exact List.mem_append_left _ hr
      · simp only [List.mem_singleton] at hr; subst hr
        exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))
  refine wp_arg hp (i := 0) hsp₉ hrd₉ (by omega) (by rw [m₉]; exact hp.arg F₃ (by omega)) fun t₁ v₁ => ?_
  have hoW : oR s₀ ∈ t₁.wr := hp.oW (by rw [v₁.wr, hwr₉])
  refine WP.append (stores_ok .r2 hp.o_fit rfl tagList t₁ v₁.gpr hoW (by decide) (by decide))
    fun t₂ ⟨hs₂, hf₂, hg₂, hrd₂, hwr₂, hsp₂⟩ => ?_
  have hfo : Frame [oR s₀] t₁.mem t₂.mem := hf₂.sub fun r hr => by
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr
    have hb : ∀ x ∈ tagList, x.2.1 + ssize x.2.2 ≤ 16 := by decide
    exact ⟨_, List.mem_singleton_self _, sub_base _ (hb x hx) (by omega)⟩
  have F₂ : Frame (offR (stB s₀) wkL ++ [oR s₀, scrR (sc s₀)]) s₀.mem t₂.mem := by
    refine F₃.trans ?_
    rw [← m₉, ← v₁.mem]
    exact hfo.mono fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact List.mem_append_right _ List.mem_cons_self
  refine wp_arg hp (i := 1) (by rw [hsp₂, v₁.sp, hsp₉]) (by rw [hrd₂, v₁.rd, hrd₉]) (by omega) (hp.arg F₂ (by omega))
    fun t₃ v₃ => ?_
  have hsv : SavedS (State.addr (sc s₀)) s₀.gpr t₃.mem := by
    intro i hi
    rw [v₃.mem, hfo.readW (Region.contains_self _ _) (by
      simp only [List.mem_singleton, forall_eq]
      exact hp.o_scr.symm.sub_left (sub_base _ (by omega) (by omega))) (by decide), v₁.mem, m₉, m₃,
      Mem.readW_writeW_sep (hp.st_scr.symm.sep (contains_off (by omega) (by omega))
        (contains_off (by omega) (by omega))) (by decide), k₁.mem]
    exact h.saved i hi
  refine WP.mono (restoreScr_ok (g := s₀.gpr) hp.sc_fit v₃.gpr (hp.scW (by rw [v₃.wr, hwr₂, v₁.wr, hwr₉])) hsv)
    fun s' ⟨hr', k'⟩ => ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · rcases preserved_cases r hr with rfl | ⟨i, hi, rfl⟩
    · rw [k'.gpr _ (by decide), v₃.other _ (by decide), hg₂, v₁.other _ (by decide), g₉ _ (by decide), h.lr]
    · exact hr' i hi
  · rw [k'.sp, v₃.sp, hsp₂, v₁.sp, hsp₉]
  · intro key msg hbuf hcnt
    obtain ⟨msg, b, rfl, hrep, hbl, hbb⟩ := Proof.Poly1305.Buffered.split hbuf
    have hkb : (msg ++ b).length % 16 = kb s₀ := by
      rw [← cnt_mod, hcnt, BitVec.toNat_ofNat]; omega
    have hb : b = Bf s₀ := by rw [← hbb, hkb]
    subst hb
    obtain ⟨hlen, hkey, hacc⟩ := hrep
    -- The tag's words.
    have wd : ∀ x ∈ tagList, ∀ d, x.2.1 = d → x.2.2 = false →
        (s'.mem.readW (oA s₀ + BitVec.ofNat 64 d) 32).toNat = (s₉.gpr x.1).toNat := by
      intro x hx d hd hb
      have := hs₂ x hx
      obtain ⟨r, o, b⟩ := x
      simp only at hd hb; subst hd hb
      have hr2 : r ≠ .r2 := by
        have : ∀ x ∈ tagList, x.1 ≠ .r2 := by decide
        exact this _ hx
      rw [k'.mem, v₃.mem]; simp only [Stored] at this; rw [this, v₁.other _ hr2]
    have e0 := wd _ (by decide : (Reg.r3, 0, false) ∈ tagList) 0 rfl rfl
    have e4 := wd _ (by decide : (Reg.r5, 4, false) ∈ tagList) 4 rfl rfl
    have e8 := wd _ (by decide : (Reg.r7, 8, false) ∈ tagList) 8 rfl rfl
    have e12 := wd _ (by decide : (Reg.r10, 12, false) ∈ tagList) 12 rfl rfl
    simp only at e0 e4 e8 e12
    rw [e3] at e0; rw [e5] at e4; rw [e7] at e8; rw [e10] at e12
    have hv : val (carryN (sumL D w) 0 9) = tw0 (carryN (sumL D w) 0 9) + 2 ^ 32 * tw1 (carryN (sumL D w) 0 9) +
        2 ^ 64 * tw2 (carryN (sumL D w) 0 9) + 2 ^ 96 * tw3 (carryN (sumL D w) 0 9) +
        2 ^ 128 * (carryN (sumL D w) 0 9 9 / 2 ^ 11) := by
      rw [val_toWords hL]; rfl
    have hvs : val (carryN (sumL D w) 0 9) = val (redL D) + (w 0 + 2 ^ 32 * w 1 + 2 ^ 64 * w 2 + 2 ^ 96 * w 3) := by
      rw [val_carryN _ 0 9 (by omega), ← val_mlimb (hw4 0) (hw4 1) (hw4 2) (hw4 3)]
      simp only [val, sumL]; ring
    -- The key.
    rw [← hkey, take_bytesAt _ _ (by omega), ← val_rlimb] at hacc
    have hlt : leNum (bytesAt s₀.mem (stB s₀) 24) < P := by rw [hacc]; exact Poly1305.accumulate_lt _ _
    have hA : accumulate (Rn s₀) msg = A0 s₀ := by rw [A0, val_accD_eq hlt]; exact hacc.symm
    have hlt' := Poly1305.absorbAll_lt (r := Rn s₀) (a := A0 s₀) (by rw [← hA]; exact Poly1305.accumulate_lt _ _)
      (Bf s₀)
    have hS : leNum (((bytesAt s₀.mem (stB s₀ + 24) 32).drop 16).take 16) =
        w 0 + 2 ^ 32 * w 1 + 2 ^ 64 * w 2 + 2 ^ 96 * w 3 := by
      rw [(drop_bytesAt s₀.mem (stB s₀ + 24) 16 16 : (bytesAt s₀.mem (stB s₀ + 24) 32).drop 16 = _),
        take_bytesAt _ _ le_rfl, leNum_bytesAt_16, show (24 : Addr) = BitVec.ofNat 64 24 from rfl, off_add, off_add,
        off_add, off_add, off_add]
    simp only [Spec.Poly1305.mac]
    rw [← hkey, take_bytesAt _ _ (by omega), ← val_rlimb, Poly1305.accumulate_append hlen, hA, hS,
      Poly1305.bytesAt_leBytes, ← Poly1305.leNum_bytesAt_read, leNum_bytesAt_16]
    rw [e0, e4, e8, e12]
    have key : tw0 (carryN (sumL D w) 0 9) + 2 ^ 32 * tw1 (carryN (sumL D w) 0 9) +
        2 ^ 64 * tw2 (carryN (sumL D w) 0 9) + 2 ^ 96 * tw3 (carryN (sumL D w) 0 9) =
        (Poly1305.absorbAll (Rn s₀) (A0 s₀) (Bf s₀) + (w 0 + 2 ^ 32 * w 1 + 2 ^ 64 * w 2 + 2 ^ 96 * w 3)) %
          256 ^ 16 := by
      rw [hvL, hDv, Nat.mod_eq_of_lt hlt'] at hvs
      rw [show (256 : Nat) ^ 16 = 2 ^ 128 by norm_num]
      have b0 := (s₉.gpr .r3).isLt; have b1 := (s₉.gpr .r5).isLt; have b2 := (s₉.gpr .r7).isLt
      have b3 := (s₉.gpr .r10).isLt
      rw [e3] at b0; rw [e5] at b1; rw [e7] at b2; rw [e10] at b3
      omega
    rw [key, Poly1305.leBytes_mod]

/-! ## The whole function -/

theorem finalize_correct {s₀ : State} (hp : FPre s₀) :
    WP isa finalize s₀ fun s' => abiPreserved s₀ s' ∧ Proof.Poly1305.finalizeArm.post s₀ s' := by
  refine WP.seq (WP.mono (prologue_ok hp) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (pad_ok hp h₁) fun s₂ h₂ => ?_)
  refine WP.seq (WP.mono (mid_ok hp h₂) fun s₃ h₃ => ?_)
  exact WP.seq (WP.mono (last_ok hp h₃) fun s₄ h₄ => tag_ok hp h₄)

/-! ## Constant time -/

/-- The initial taint: `r0` (`state`) and `r2:r3` (`count`) are public, `r0`
points at the state, and the 8 bytes of stack arguments are public, the
second one pointing at `scratch`. The analysis tracks the public slots of
the state (the buffer's length). -/
def τf : VG.Arm.Taint.T :=
  { regs := .ofList [.r0, .r2, .r3], flags := false, lens := [128, 16, 128], bases := [(.r0, 0)], argLen := 8,
    argBases := [(4, 2)] }

theorem argByte_eq {s : State} (hsp : s.sp.toNat + 8 ≤ 2 ^ 32) {k : Nat} (hk : k < 8) :
    VG.Arm.Taint.argByte s k = stackArgAddr s (k / 4) + BitVec.ofNat 64 (k % 4) := by
  simp only [VG.Arm.Taint.argByte, stackArgAddr]
  rw [addr_add (by omega), BitVec.add_assoc, ← BitVec.ofNat_add]
  congr 2; omega

theorem wff {s : State} (h : Proof.Poly1305.finalizeArm.pre s) : VG.Arm.Taint.Wf τf s := by
  have hp := FPre.of s h
  have hst := hp.st_fit; have ho := hp.o_fit; have hsc := hp.sc_fit; have hs := hp.sp_fit
  refine ⟨fun _ => ⟨by simp [hp.wr, τf], ?_, ?_⟩, ?_, fun _ => ⟨hs, ?_⟩, ?_⟩
  · simp only [hp.wr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, List.Pairwise.nil, and_true]
    exact ⟨⟨hp.st_o, hp.st_scr⟩, hp.o_scr, fun _ h => h.elim⟩
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl) <;> simp only [addr_toNat] <;> omega
  · intro p hp'; simp only [τf, List.mem_singleton] at hp'; subst hp'; simp [VG.Arm.Taint.region, hp.wr]
  · have e : (⟨State.addr s.sp, 8⟩ : Region) = argR s := by simp [stackArgAddr]
    simp only [τf, e, hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact hp.a_st
    · exact hp.a_o
    · exact hp.a_scr
  · intro p hp'; simp only [τf, List.mem_singleton] at hp'; subst hp'
    refine ⟨by decide, ?_⟩
    simp only [VG.Arm.Taint.region, hp.wr]
    rfl

theorem agreef {s₁ s₂ : State} (h₁ : Proof.Poly1305.finalizeArm.pre s₁) (h₂ : Proof.Poly1305.finalizeArm.pre s₂)
    (hpub : Proof.Poly1305.finalizeArm.pub s₁ s₂) : VG.Arm.Taint.Agree τf s₁ s₂ := by
  obtain ⟨psp, p0, p2, p3, a0, a1⟩ := hpub
  have hp₁ := FPre.of s₁ h₁; have hp₂ := FPre.of s₂ h₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, wff h₁, wff h₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun _ => psp, fun k hk => ?_⟩
  · simp only [τf, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> assumption
  · rw [hp₁.wr, hp₂.wr]; simp only [stR, oR, oA, oP, scrR, sc, p0, a0, a1]
  · simp only [τf] at hk
    rw [argByte_eq hp₁.sp_fit hk, argByte_eq hp₂.sp_fit hk, Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by omega)),
      Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by omega))]
    have : k / 4 = 0 ∨ k / 4 = 1 := by omega
    rcases this with h | h <;> rw [h]
    · exact congrArg _ a0
    · exact congrArg _ a1

/-- A state satisfying the precondition: `out` at `0x2000` and `scratch` at
`0x3000`, passed on the stack at `0x5000`. -/
def finalizeSat : State where
  gpr r := match r with
    | .r0 => 0x1000 | _ => 0
  sp := 0x5000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x5001 then 0x20 else if a = 0x5005 then 0x30 else 0
  rd := [⟨0x5000, 8⟩]
  wr := [⟨0x1000, 128⟩, ⟨0x2000, 16⟩, ⟨0x3000, 128⟩]

theorem finalize_verified : Verified Arm.target finalize Proof.Poly1305.finalizeArm := by
  refine ⟨fun s hs => finalize_correct (FPre.of s hs), ?_, ?_⟩
  · exact VG.Taint.constantTime (A := taint) τf (fun _ _ h₁ h₂ hp => agreef h₁ h₂ hp) (by taint_decide)
  · have e0 : stackArg finalizeSat 0 = 0x2000 := by decide
    have e1 : stackArg finalizeSat 1 = 0x3000 := by decide
    refine ⟨finalizeSat, ?_⟩
    simp only [Proof.Poly1305.finalizeArm, e0, e1]
    refine ⟨by simp [finalizeSat, stackArgAddr]; decide, rfl, ?_, ?_, ?_, ?_, ?_, ?_, by decide, by decide,
      by decide, by decide⟩ <;>
    · intro a h₁ h₂
      simp only [Region.Contains, finalizeSat, stackArgAddr, State.addr] at h₁ h₂
      bv_omega

end VG.Proof.Poly1305.Arm.Fin
