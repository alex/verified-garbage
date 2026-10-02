import VerifiedGarbage.Proof.Poly1305.Arm.Steps
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Spec.Poly1305.Contract
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.Omega

/-!
# Poly1305 on 32-bit ARM: `update`

The callee-saved registers are saved in `scratch` (`prologue_ok`); a non-empty
buffer is filled with the first `nf` bytes of the data (`fill_ok`); the data
pointer, lengths and counts are stored in the state's working space, the limbs
of `r` computed and the accumulator loaded (`mid_ok`); a full buffer is
absorbed (`buf_ok`), then the whole blocks of the rest of the data
(`loop_ok`); the accumulator is stored (`epi_ok`), and the last bytes of the
data are copied into the buffer (`rest_ok`). Throughout (`UC`), only the
state's working space, the buffer, the accumulator and `scratch` change.
-/

open VG.PowLit

namespace VG.Proof.Poly1305.Arm.Update

open VG VG.Arm VG.Impl.Poly1305.Arm VG.Proof.Poly1305.Arm
open VG.Spec.Poly1305 (P clamp leNum bytesAt accumulate Repr Buffered)

/-! ## The precondition -/

section
variable (s₀ : State)
/-- `data`, its length and region, and `scratch`. -/
abbrev dp : BitVec 32 := stackArg s₀ 0
abbrev dl : Nat := (stackArg s₀ 1).toNat
abbrev dA : Addr := State.addr (dp s₀)
abbrev dR : Region := ⟨dA s₀, dl s₀⟩
abbrev sc : BitVec 32 := stackArg s₀ 2
/-- The stack arguments. -/
abbrev argR : Region := ⟨stackArgAddr s₀ 0, 12⟩
/-- The number of bytes buffered, and the bytes. -/
abbrev kb : Nat := (s₀.gpr .r2).toNat % 16
abbrev Bf : List Byte := bytesAt s₀.mem (stB s₀ + 56) (kb s₀)
/-- The first `c` bytes of data, and the `n` from byte `c` on. -/
abbrev Dt (c : Nat) : List Byte := bytesAt s₀.mem (dA s₀) c
abbrev Dd (c n : Nat) : List Byte := bytesAt s₀.mem (dA s₀ + BitVec.ofNat 64 c) n
/-- The number of bytes the buffer is filled with. -/
def nf : Nat := if kb s₀ = 0 then 0 else min (16 - kb s₀) (dl s₀)
/-- The number of whole blocks after that, and of bytes left. -/
abbrev nw : Nat := (dl s₀ - nf s₀) / 16
abbrev nr : Nat := (dl s₀ - nf s₀) % 16
/-- The blocks absorbed from the buffer (if it is filled), and the bytes left in it (if not). -/
def X1 : List Byte := if kb s₀ + nf s₀ = 16 then Bf s₀ ++ Dt s₀ (nf s₀) else []
def Y0 : List Byte := if kb s₀ + nf s₀ = 16 then [] else Bf s₀ ++ Dt s₀ (nf s₀)
end

structure UPre (s₀ : State) : Prop where
  rd : s₀.rd = [dR s₀, argR s₀]
  wr : s₀.wr = [stR (s₀.gpr .r0), scrR (sc s₀)]
  st_scr : (stR (s₀.gpr .r0)).Disjoint (scrR (sc s₀))
  d_st : (dR s₀).Disjoint (stR (s₀.gpr .r0))
  d_scr : (dR s₀).Disjoint (scrR (sc s₀))
  a_st : (argR s₀).Disjoint (stR (s₀.gpr .r0))
  a_scr : (argR s₀).Disjoint (scrR (sc s₀))
  st_fit : (s₀.gpr .r0).toNat + 128 ≤ 2 ^ 32
  d_fit : (dp s₀).toNat + dl s₀ ≤ 2 ^ 32
  sc_fit : (sc s₀).toNat + 128 ≤ 2 ^ 32
  sp_fit : s₀.sp.toNat + 12 ≤ 2 ^ 32

theorem UPre.of (s : State) (h : Proof.Poly1305.updateArm.pre s) : UPre s := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩

theorem kb_lt (s₀ : State) : kb s₀ < 16 := Nat.mod_lt _ (by decide)

theorem dl_lt (s₀ : State) : dl s₀ < 2 ^ 32 := (stackArg s₀ 1).isLt

/-- What filling the buffer does. -/
theorem nf_facts (s₀ : State) :
    nf s₀ ≤ dl s₀ ∧ kb s₀ + nf s₀ ≤ 16 ∧ (kb s₀ = 0 → nf s₀ = 0) ∧
      (0 < kb s₀ → kb s₀ + nf s₀ < 16 → nf s₀ = dl s₀) := by
  have := kb_lt s₀
  simp only [nf]
  split <;> omega

/-! ## What holds throughout -/

/-- The state's working space and buffer (`wkL`) and `scratch`. -/
abbrev uF (s₀ : State) : List Region := offR (stB s₀) wkL ++ [scrR (sc s₀)]

structure UC (s₀ s : State) : Prop where
  r0 : s.gpr .r0 = s₀.gpr .r0
  lr : s.gpr .lr = s₀.gpr .lr
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : Frame (uF s₀) s₀.mem s.mem
  saved : SavedS (State.addr (sc s₀)) s₀.gpr s.mem

theorem UPre.stW {s₀ : State} (hp : UPre s₀) {s : State} (h : s.wr = s₀.wr) : stR (s₀.gpr .r0) ∈ s.wr := by
  rw [h, hp.wr]; exact List.mem_cons_self

theorem UPre.scW {s₀ : State} (hp : UPre s₀) {s : State} (h : s.wr = s₀.wr) : scrR (sc s₀) ∈ s.wr := by
  rw [h, hp.wr]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _)

/-- A range of the state is disjoint from `scratch`. -/
theorem UPre.st_scr' {s₀ : State} (hp : UPre s₀) {a n : Nat} (h : a + n ≤ 128) :
    (⟨stB s₀ + BitVec.ofNat 64 a, n⟩ : Region).Disjoint (scrR (sc s₀)) :=
  hp.st_scr.sub_left (sub_base _ h (by decide))

/-- Changing only ranges `l` of the state within `wkL`, and registers other
than `r0` and `lr`, keeps `UC`. -/
theorem UC.keepsF {s₀ : State} (hp : UPre s₀) {s s' : State} (h : UC s₀ s) {ws : List Reg}
    {l : List (Nat × Nat)} (hk : KeepsF ws (offR (stB s₀) l) s s') (hws : Reg.r0 ∉ ws ∧ Reg.lr ∉ ws)
    (hl : (l.all fun p => wkL.any fun q => q.1 ≤ p.1 ∧ p.1 + p.2 ≤ q.1 + q.2) = true)
    (hl' : (l.all fun p => p.1 + p.2 ≤ 128) = true) : UC s₀ s' where
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
      exact ((hp.st_scr' this).symm.sub_left (sub_base _ (by omega_using [hi]) (by decide)))) (by decide)]
    exact h.saved i hi

theorem UC.upd {s₀ s s' : State} (h : UC s₀ s) {d : Reg} {v : BitVec 32} (u : Upd s s' d v)
    (hd : d ≠ .r0 ∧ d ≠ .lr) : UC s₀ s' :=
  ⟨by rw [u.other _ (Ne.symm hd.1), h.r0], by rw [u.other _ (Ne.symm hd.2), h.lr], u.rd.trans h.rd,
    u.wr.trans h.wr, u.sp.trans h.sp, by rw [u.mem]; exact h.frame, by rw [u.mem]; exact h.saved⟩

theorem UC.flags {s₀ s s' : State} (h : UC s₀ s) (u : Fupd s s') : UC s₀ s' :=
  ⟨by rw [u.gpr, h.r0], by rw [u.gpr, h.lr], u.rd.trans h.rd, u.wr.trans h.wr, u.sp.trans h.sp,
    by rw [u.mem]; exact h.frame, by rw [u.mem]; exact h.saved⟩

/-- The address of stack argument `i`. -/
theorem argAddr {s₀ : State} (hp : UPre s₀) {i : Nat} (hi : i < 3) :
    stackArgAddr s₀ i = stackArgAddr s₀ 0 + BitVec.ofNat 64 (4 * i) := by
  have := hp.sp_fit
  simp only [stackArgAddr]
  rw [addr_add (by omega_using [hi, this]), addr_add (by omega_using [this])]
  simp

/-- The stack arguments are unchanged. -/
theorem UC.arg {s₀ : State} (hp : UPre s₀) {s : State} (h : UC s₀ s) {i : Nat} (hi : i < 3) :
    s.mem.readW (stackArgAddr s₀ i) 32 = stackArg s₀ i := by
  rw [stackArg, h.frame.readW (r := argR s₀) (by rw [argAddr hp hi]; exact contains_off (by omega_using [hi]) (by omega_using [hi]))
    (fun r hr => ?_) (by decide)]
  rcases List.mem_append.mp hr with hr | hr
  · obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hr
    simp only [wkL, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl <;> exact hp.a_st.sub_right (sub_base _ (by decide) (by decide))
  · simp only [List.mem_singleton] at hr; subst hr; exact hp.a_scr

/-- Loading stack argument `i`. -/
theorem wp_arg' {s₀ : State} (hp : UPre s₀) {s : State} (hsp : s.sp = s₀.sp) (hrd : s.rd = s₀.rd) {i : Nat}
    (hi : i < 3) (hm : s.mem.readW (stackArgAddr s₀ i) 32 = stackArg s₀ i) {t : Reg}
    {is : List Instr} {Q : State → Prop}
    (k : ∀ s', Upd s s' t (stackArg s₀ i) → WP isa (.block is) s' Q) :
    WP isa (.block (.ldrSp t (4 * i) :: is)) s Q := by
  have := hp.sp_fit
  refine wp_ldrSp (a := stackArgAddr s₀ i) (by omega_using [hi]) (by rw [hsp]; rfl)
    (by rw [hrd, hp.rd, argAddr hp hi]
        exact ⟨_, List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)),
          contains_off (by omega_using [hi]) (by omega_using [hi])⟩) fun s' u => ?_
  rw [hm] at u
  exact k s' u

theorem wp_arg {s₀ : State} (hp : UPre s₀) {s : State} (h : UC s₀ s) {i : Nat} (hi : i < 3) {t : Reg}
    {is : List Instr} {Q : State → Prop}
    (k : ∀ s', Upd s s' t (stackArg s₀ i) → WP isa (.block is) s' Q) :
    WP isa (.block (.ldrSp t (4 * i) :: is)) s Q :=
  wp_arg' hp h.sp h.rd hi (h.arg hp hi) k

/-- Data bytes are unchanged. -/
theorem UC.data {s₀ : State} (hp : UPre s₀) {s : State} (h : UC s₀ s) {i : Nat} (hi : i < dl s₀) :
    s.mem (dA s₀ + BitVec.ofNat 64 i) = s₀.mem (dA s₀ + BitVec.ofNat 64 i) :=
  h.frame.bytes (R := dR s₀) (fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hr
      simp only [wkL, List.mem_cons, List.not_mem_nil, or_false] at hp'
      rcases hp' with rfl | rfl <;> exact hp.d_st.sub_right (sub_base _ (by decide) (by decide))
    · simp only [List.mem_singleton] at hr; subst hr; exact hp.d_scr)
    (by have := dl_lt s₀; show dl s₀ ≤ 2 ^ 64; omega_using [this]) hi

/-! ## Prologue -/

theorem sub0 (x : BitVec 32) : x - 0 = x := by simp

theorem and15 (x : BitVec 32) : x &&& (15 : BitVec 32) = BitVec.ofNat 32 (x.toNat % 16) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (15 : BitVec 32).toNat = 2 ^ 4 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := x.toNat % 16) (by omega_using [])]

/-- After the prologue. -/
structure P1 (s₀ s : State) : Prop extends UC s₀ s where
  sfr : Frame [scrR (sc s₀)] s₀.mem s.mem
  r4 : s.gpr .r4 = BitVec.ofNat 32 (kb s₀)
  r5 : s.gpr .r5 = dp s₀
  r6 : s.gpr .r6 = BitVec.ofNat 32 (dl s₀)
  z : s.z = decide (kb s₀ = 0)

theorem prologue_ok {s₀ : State} (hp : UPre s₀) :
    WP isa (.block (([.ldrSp .r12 8] : List Instr) ++ saveScr ++
      ([.dp .and .r4 .r2 (.imm 15), .ldrSp .r5 0, .ldrSp .r6 4, .cmp .r4 (.imm 0)] : List Instr))) s₀ (P1 s₀) := by
  have hsc := hp.sc_fit
  refine wp_arg' (i := 2) hp rfl rfl (by decide) rfl fun s₁ u₁ => ?_
  refine WP.append (saveScr_ok hsc u₁.gpr (by rw [u₁.wr]; exact hp.scW rfl))
    fun s₂ ⟨hsv, hf₂, hg₂, hrd₂, hwr₂, hsp₂⟩ => ?_
  have hf₂' : Frame [scrR (sc s₀)] s₀.mem s₂.mem := by
    rw [← u₁.mem]; exact hf₂.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by decide)⟩
  have uc₂ : UC s₀ s₂ :=
    ⟨by rw [hg₂, u₁.other _ (by decide)], by rw [hg₂, u₁.other _ (by decide)], by rw [hrd₂, u₁.rd],
      by rw [hwr₂, u₁.wr], by rw [hsp₂, u₁.sp], hf₂'.mono fun _ hr => List.mem_append_right _ hr,
      fun i hi => by rw [hsv i hi, u₁.other _ (by revert i; decide)]⟩
  refine wp_and (op2_imm (by decide)) fun s₃ u₃ => ?_
  have uc₃ := uc₂.upd u₃ (by decide)
  refine wp_arg (i := 0) hp uc₃ (by decide) fun s₄ u₄ => ?_
  have uc₄ := uc₃.upd u₄ (by decide)
  refine wp_arg (i := 1) hp uc₄ (by decide) fun s₅ u₅ => ?_
  have uc₅ := uc₄.upd u₅ (by decide)
  refine wp_cmp (op2_imm (by decide)) fun s₆ u₆ hz => WP.block_nil ?_
  have hr4 : s₅.gpr .r4 = BitVec.ofNat 32 (kb s₀) := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, hg₂, u₁.other _ (by decide)]
    exact and15 _
  refine ⟨uc₅.flags u₆, by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem]; exact hf₂', by rw [u₆.gpr, hr4],
    by rw [u₆.gpr, u₅.other _ (by decide), u₄.gpr], by rw [u₆.gpr, u₅.gpr]; simp, ?_⟩
  rw [hz, hr4, sub0, ofNat_beq_zero (by have := kb_lt s₀; omega_using [this])]

/-! ## Filling the buffer -/

theorem shr4_beq (x : BitVec 32) : (x >>> 4 - 0 == 0) = decide (x.toNat < 16) := by
  rw [sub0]
  by_cases h : x.toNat < 16
  · have : x >>> 4 = 0 := BitVec.eq_of_toNat_eq (by rw [toNat_shr]; simp; omega_using [h])
    simp [this, h]
  · have : x >>> 4 ≠ 0 := fun e => h (by have := congrArg BitVec.toNat e; rw [toNat_shr] at this; simp at this; omega_using [this])
    rw [beq_eq_false_iff_ne.mpr this]; simp [h]

theorem sub_ofNat32 {a b : Nat} (h : b ≤ a) :
    BitVec.ofNat 32 a - BitVec.ofNat 32 b = BitVec.ofNat 32 (a - b) := by
  rw [show BitVec.ofNat 32 a = BitVec.ofNat 32 (a - b) + BitVec.ofNat 32 b by
    rw [← BitVec.ofNat_add, Nat.sub_add_cancel h], BitVec.add_sub_cancel]

theorem CopyInv.keepsF {sI : State} {st src : BitVec 32} {j0 : Nat} {xs : List Byte} (hj0 : j0 + xs.length ≤ 16)
    {s : State} (h : CopyInv sI st src j0 xs xs.length s) :
    KeepsF [.r1, .r5, .r8, .r12] (offR (State.addr st) [(56, 16)]) sI s :=
  ⟨h.keep, h.frame hj0, h.rd, h.wr, h.sp⟩

/-- `r8 := min(16 - kb, dl)`. -/
theorem fillCount_ok {s₀ : State} (hk : 0 < kb s₀) {s : State} (h4 : s.gpr .r4 = BitVec.ofNat 32 (kb s₀))
    (h6 : s.gpr .r6 = BitVec.ofNat 32 (dl s₀)) :
    WP isa fillCount s fun s' => s'.gpr .r8 = BitVec.ofNat 32 (nf s₀) ∧ Keeps [.r8, .r12] s s' := by
  have hkb := kb_lt s₀
  have hdl := dl_lt s₀
  have hnf : nf s₀ = min (16 - kb s₀) (dl s₀) := by simp only [nf]; rw [iteF (by omega_using [hk, hkb])]
  have e16 : (16 : BitVec 32) = BitVec.ofNat 32 16 := rfl
  refine WP.seq (WP.mono (Q := fun s' : State => s'.gpr .r8 = BitVec.ofNat 32 (16 - kb s₀) ∧
    s'.z = decide (dl s₀ < 16) ∧ Keeps [.r8, .r12] s s') ?_ fun s₄ ⟨h8, hz, k₄⟩ => ?_)
  · refine wp_mov (op2_imm (by decide)) fun s₁ u₁ => wp_sub (op2_reg _ _) fun s₂ u₂ => ?_
    refine wp_mov (op2_lsr (by decide)) fun s₃ u₃ => wp_cmp (op2_imm (by decide)) fun s₄ u₄ hz =>
      WP.block_nil ⟨?_, ?_, ?_⟩
    · rw [u₄.gpr, u₃.other _ (by decide), u₂.gpr, u₁.gpr, u₁.other _ (by decide), h4, e16,
        sub_ofNat32 (by omega_using [hk, hkb])]
    · rw [hz, u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), h6, shr4_beq, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt hdl]
    · exact (u₁.keeps (by simp)).trans ((u₂.keeps (by simp)).trans ((u₃.keeps (by simp)).trans (u₄.keeps _)))
  refine WP.ite s₄.z (eval_eq _) (fun hb => ?_) (fun hb => WP.block_nil ⟨?_, k₄⟩)
  · have hd : dl s₀ < 16 := by rw [hz] at hb; simpa using hb
    have h6' : s₄.gpr .r6 = BitVec.ofNat 32 (dl s₀) := by rw [k₄.gpr _ (by decide), h6]
    have h4' : s₄.gpr .r4 = BitVec.ofNat 32 (kb s₀) := by rw [k₄.gpr _ (by decide), h4]
    refine WP.seq (WP.mono (Q := fun s' : State => s'.z = decide (dl s₀ + kb s₀ < 16) ∧ Keeps [.r12] s₄ s') ?_
      fun s₅ ⟨hz₅, k₅⟩ => ?_)
    · refine wp_add (op2_reg _ _) fun t₁ v₁ => wp_mov (op2_lsr (by decide)) fun t₂ v₂ =>
        wp_cmp (op2_imm (by decide)) fun t₃ v₃ hz' => WP.block_nil ⟨?_, ?_⟩
      · rw [hz', v₂.gpr, v₁.gpr, h6', h4', ← BitVec.ofNat_add, shr4_beq, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by omega_using [hk, hkb, hdl, hd])]
      · exact (v₁.keeps (by simp)).trans ((v₂.keeps (by simp)).trans (v₃.keeps _))
    refine WP.ite s₅.z (eval_eq _) (fun hb' => ?_) (fun hb' => WP.block_nil ⟨?_, ?_⟩)
    · have hd' : dl s₀ + kb s₀ < 16 := by rw [hz₅] at hb'; simpa using hb'
      refine wp_mov (op2_reg _ _) fun t₁ v₁ => WP.block_nil ⟨?_, ?_⟩
      · rw [v₁.gpr, k₅.gpr _ (by decide), h6', hnf, Nat.min_eq_right (by omega_using [hk, hkb, hd'])]
      · exact k₄.trans ((k₅.mono (by simp)).trans (v₁.keeps (by simp)))
    · have hd' : ¬ dl s₀ + kb s₀ < 16 := by rw [hz₅] at hb'; simpa using hb'
      rw [k₅.gpr _ (by decide), h8, hnf, Nat.min_eq_left (by omega_using [hk, hkb, hd'])]
    · exact k₄.trans (k₅.mono (by simp))
  · have hd : ¬ dl s₀ < 16 := by rw [hz] at hb; simpa using hb
    rw [h8, hnf, Nat.min_eq_left (by omega_using [hk, hkb, hdl, hd])]

theorem UC.keeps {s₀ s s' : State} (h : UC s₀ s) {ws : List Reg} (k : Keeps ws s s')
    (hws : Reg.r0 ∉ ws ∧ Reg.lr ∉ ws) : UC s₀ s' :=
  ⟨by rw [k.gpr _ hws.1, h.r0], by rw [k.gpr _ hws.2, h.lr], k.rd.trans h.rd, k.wr.trans h.wr, k.sp.trans h.sp,
    by rw [k.mem]; exact h.frame, by rw [k.mem]; exact h.saved⟩

/-- After filling the buffer. -/
structure F2 (s₀ s : State) : Prop extends UC s₀ s where
  sfr : Frame (offR (stB s₀) [(56, 16)] ++ [scrR (sc s₀)]) s₀.mem s.mem
  r4 : s.gpr .r4 = BitVec.ofNat 32 (kb s₀ + nf s₀)
  r5 : s.gpr .r5 = dp s₀ + BitVec.ofNat 32 (nf s₀)
  r6 : s.gpr .r6 = BitVec.ofNat 32 (dl s₀ - nf s₀)
  buf : bytesAt s.mem (stB s₀ + 56) (kb s₀ + nf s₀) = Bf s₀ ++ Dt s₀ (nf s₀)

theorem fill_ok {s₀ : State} (hp : UPre s₀) {s : State} (h : P1 s₀ s) :
    WP isa (.ite .eq (.block []) fill) s (F2 s₀) := by
  obtain ⟨hn1, hn2, hn3, hn4⟩ := nf_facts s₀
  have hkb := kb_lt s₀
  have hdl := dl_lt s₀
  have hfit := hp.st_fit
  have hdf := hp.d_fit
  refine WP.ite s.z (eval_eq _) (fun hb => WP.block_nil ?_) (fun hb => ?_)
  · have hk : kb s₀ = 0 := by rw [h.z] at hb; simpa using hb
    have hn : nf s₀ = 0 := hn3 hk
    refine ⟨h.toUC, h.sfr.mono fun _ hr => List.mem_append_right _ hr, by rw [h.r4, hk, hn],
      by rw [h.r5, hn]; simp, by rw [h.r6, hn, Nat.sub_zero], ?_⟩
    simp only [Bf, Dt, hk, hn, Nat.add_zero, bytesAt, List.range_zero, List.map_nil, List.append_nil]
  have hk : 0 < kb s₀ := by
    rw [h.z] at hb; simp only [decide_eq_false_iff_not] at hb; omega_using [hkb, hb]
  refine WP.seq (WP.mono (fillCount_ok hk h.r4 h.r6) fun s₁ ⟨h8, k₁⟩ => ?_)
  refine WP.seq (wp_sub (op2_reg _ _) fun s₂ u₂ => wp_add (op2_reg _ _) fun s₃ u₃ =>
    wp_add (op2_reg _ _) fun s₄ u₄ => wp_cmp (op2_imm (by decide)) fun s₅ u₅ hz => WP.block_nil ?_)
  have uc₅ : UC s₀ s₅ := (((h.toUC.keeps k₁ (by decide)).upd u₂ (by decide)).upd u₃ (by decide)).upd u₄
    (by decide) |>.flags u₅
  have m₅ : s₅.mem = s.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, k₁.mem]
  have g₅ : ∀ r, r ∉ [Reg.r1, .r4, .r6, .r8, .r12] → s₅.gpr r = s.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u₅.gpr, u₄.other _ hr.2.1, u₃.other _ hr.1, u₂.other _ hr.2.2.1, k₁.gpr _ (by simp [hr.2.2.2.1, hr.2.2.2.2])]
  have e8 : s₅.gpr .r8 = BitVec.ofNat 32 (nf s₀) := by
    rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), h8]
  have e8' : s₄.gpr .r8 = BitVec.ofNat 32 (nf s₀) := by rw [← u₅.gpr]; exact e8
  have e4 : s₅.gpr .r4 = BitVec.ofNat 32 (kb s₀ + nf s₀) := by
    rw [u₅.gpr, u₄.gpr, u₃.other .r4 (by decide), u₂.other .r4 (by decide), u₃.other .r8 (by decide),
      u₂.other .r8 (by decide), h8, k₁.gpr .r4 (by decide), h.r4, ← BitVec.ofNat_add]
  have e6 : s₅.gpr .r6 = BitVec.ofNat 32 (dl s₀ - nf s₀) := by
    rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, k₁.gpr .r6 (by decide), h.r6, h8,
      sub_ofNat32 hn1]
  have e1 : s₅.gpr .r1 = s₀.gpr .r0 + BitVec.ofNat 32 (kb s₀) := by
    rw [u₅.gpr, u₄.other _ (by decide), u₃.gpr, u₂.other .r0 (by decide), u₂.other .r4 (by decide),
      k₁.gpr .r0 (by decide), k₁.gpr .r4 (by decide), h.r0, h.r4]
  have e5 : s₅.gpr .r5 = dp s₀ := by rw [g₅ _ (by decide), h.r5]
  have hBf : bytesAt s₅.mem (stB s₀ + 56) (kb s₀) = Bf s₀ := by
    rw [m₅]
    exact bytesAt_frame h.sfr (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.st_scr' (a := 56) (n := kb s₀) (by omega_using [hkb, hk])) (by omega_using [hkb, hk])
  refine WP.ite s₅.z (eval_eq _) (fun hb' => WP.block_nil ?_) (fun hb' => ?_)
  · have hn : nf s₀ = 0 := by
      rw [hz, e8', sub0, ofNat_beq_zero (by omega_using [hn2, hkb, hk])] at hb'; simpa using hb'
    refine ⟨uc₅, by rw [m₅]; exact h.sfr.mono fun _ hr => List.mem_append_right _ hr, e4,
      by rw [e5, hn]; simp, e6, ?_⟩
    rw [hn, Nat.add_zero, hBf]
    simp [Dt, bytesAt]
  · have hn : 0 < nf s₀ := by
      rw [hz, e8', sub0, ofNat_beq_zero (by omega_using [hn2, hkb, hk])] at hb'; simp at hb'; omega_using [hb']
    have hl : (Dt s₀ (nf s₀)).length = nf s₀ := Poly1305.length_bytesAt _ _ _
    have hS : SrcOk s₅ (stB s₀) (dp s₀) (Dt s₀ (nf s₀)) := by
      intro i hi
      rw [hl] at hi
      refine ⟨?_, fun hc => ?_, ?_⟩
      · rw [uc₅.rd, hp.rd]
        exact ⟨_, List.mem_append_left _ (List.mem_cons_self), contains_off (by omega_using [hn1, hl, hi]) (by omega_using [hn2, hkb, hk, hn, hl, hi])⟩
      · exact hp.d_st _ (contains_off (by omega_using [hn1, hl, hi]) (by omega_using [hn2, hkb, hk, hn, hl, hi])) (sub_base _ (by decide) (by decide) _ hc)
      · rw [uc₅.data hp (by omega_using [hn1, hl, hi])]
        simp [Dt, bytesAt, List.getD_eq_getElem?_getD, hi]
    refine WP.mono (copy_ok hfit (sI := s₅) (j0 := kb s₀) (by omega_using [hn2, hl]) (by rw [hl]; omega_using [hn1, hdf, hl]) (by omega_using [hn, hl])
      (hp.stW uc₅.wr) hS e5 e1 (by rw [e8, hl])) fun s₆ hc => ?_
    have k₆ := CopyInv.keepsF (by omega_using [hn2, hl]) hc
    refine ⟨uc₅.keepsF hp k₆ (by decide) (by decide) (by decide), ?_, by rw [k₆.gpr _ (by decide), e4], ?_,
      by rw [k₆.gpr _ (by decide), e6], ?_⟩
    · have f₅ : Frame (offR (stB s₀) [(56, 16)] ++ [scrR (sc s₀)]) s₀.mem s₅.mem := by
        rw [m₅]; exact h.sfr.mono fun _ hr => List.mem_append_right _ hr
      exact f₅.trans (k₆.frame.mono fun _ hr => List.mem_append_left _ hr)
    · rw [hc.r5, hl]
    · rw [show kb s₀ + nf s₀ = kb s₀ + (Dt s₀ (nf s₀)).length by rw [hl], CopyInv.buf (by omega_using [hn2, hl]) hc, hBf]

/-! ## The working space, the limbs of `r` and the accumulator -/

theorem toNat_add_ofNat {a : BitVec 32} {k : Nat} (h : a.toNat + k < 2 ^ 32) :
    (a + BitVec.ofNat 32 k).toNat = a.toNat + k := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := k) (by omega_using [h]), Nat.mod_eq_of_lt h]

theorem sub_beq32 {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    (BitVec.ofNat 32 a - BitVec.ofNat 32 b == 0) = decide (a = b) := by
  by_cases h : a = b
  · simp [h]
  · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro h'
    apply h
    have := congrArg BitVec.toNat h'
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha,
      Nat.mod_eq_of_lt hb] at this
    change _ = 0 at this
    omega_using [ha, hb, this]

/-- A word of the state outside the buffer, after filling it. -/
theorem sfr_word {s₀ : State} (hp : UPre s₀) {m : Mem}
    (hf : Frame (offR (stB s₀) [(56, 16)] ++ [scrR (sc s₀)]) s₀.mem m) {d : Nat}
    (hd : d + 4 ≤ 56 ∨ 72 ≤ d ∧ d + 4 ≤ 128) :
    m.readW (stB s₀ + BitVec.ofNat 64 d) 32 = s₀.mem.readW (stB s₀ + BitVec.ofNat 64 d) 32 :=
  hf.readW (Region.contains_self _ _) (fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · simp only [offR, List.map_cons, List.map_nil, List.mem_singleton] at hr; subst hr
      exact disjoint_sub _ (by omega_using [hd]) (by omega_using [hd]) (by decide)
    · simp only [List.mem_singleton] at hr; subst hr
      exact hp.st_scr' (by omega_using [hd])) (by decide)

/-- After storing the working space, computing the limbs of `r` and loading the accumulator. -/
structure F3 (s₀ s : State) : Prop extends UC s₀ s where
  acc : Acc (s₀.gpr .r0) (Rl s₀) (A0 s₀) [] s
  ptr : s.mem.readW (stB s₀ + BitVec.ofNat 64 124) 32 = dp s₀ + BitVec.ofNat 32 (nf s₀)
  len : s.mem.readW (stB s₀ + BitVec.ofNat 64 76) 32 = BitVec.ofNat 32 (dl s₀ - nf s₀)
  cnt : s.mem.readW (stB s₀ + BitVec.ofNat 64 20) 32 = BitVec.ofNat 32 (nw s₀)
  buf : bytesAt s.mem (stB s₀ + 56) (kb s₀ + nf s₀) = Bf s₀ ++ Dt s₀ (nf s₀)
  z : s.z = decide (kb s₀ + nf s₀ = 16)

/-- The stores of the working space. -/
def wsList : List (Reg × Nat × Bool) := [(.r5, 124, false), (.r6, 76, false), (.r1, 20, false), (.r4, 72, false)]

theorem mid_ok {s₀ : State} (hp : UPre s₀) {s : State} (h : F2 s₀ s) :
    WP isa (.block (([.mov .r1 (.shifted .r6 .lsr 4), .str .r5 .r0 ptrOff, .str .r6 .r0 lenOff,
      .str .r1 .r0 cntOff, .str .r4 .r0 fillOff] : List Instr) ++ setupR ++ loadAcc ++
      ([.ldr .r1 .r0 fillOff, .cmp .r1 (.imm 16)] : List Instr))) s (F3 s₀) := by
  have hfit := hp.st_fit
  obtain ⟨hn1, hn2, -, -⟩ := nf_facts s₀
  have hdl := dl_lt s₀
  have hw := hp.stW h.wr
  rw [List.cons_append]
  refine wp_mov (op2_lsr (by decide)) fun s₁ u₁ => ?_
  have e1 : s₁.gpr .r1 = BitVec.ofNat 32 (nw s₀) := by
    rw [u₁.gpr, h.r6]
    apply BitVec.eq_of_toNat_eq
    rw [toNat_shr, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    simp only [nw]
    omega_using [hn1, hdl]
  have uc₁ := h.toUC.upd u₁ (by decide)
  refine WP.append (l := wsList.map (storeI .r0)) (stores_ok .r0 hfit rfl wsList s₁
    (by rw [u₁.other _ (by decide), h.r0]) (by rw [u₁.wr]; exact hw) (by decide) (by decide))
    fun s₂ ⟨hs₂, hf₂, hg₂, hrd₂, hwr₂, hsp₂⟩ => ?_
  have f₂ : Frame (offR (stB s₀) [(124, 4), (76, 4), (20, 4), (72, 4)]) s₁.mem s₂.mem := hf₂
  have uc₂ : UC s₀ s₂ := uc₁.keepsF hp (ws := []) ⟨fun r _ => by rw [hg₂], f₂, hrd₂, hwr₂, hsp₂⟩
    (by decide) (by decide) (by decide)
  refine WP.append (setupAcc_ok hfit uc₂.r0 (hp.stW uc₂.wr)) fun s₃ ⟨hr₃, hc₃, k₃⟩ => ?_
  have uc₃ : UC s₀ s₃ := uc₂.keepsF hp k₃ (by decide) (by decide) (by decide)
  refine wp_ldr (a := stB s₀ + BitVec.ofNat 64 72) (by decide) (by rw [uc₃.r0]; exact ea hfit (off := 72) (by decide))
    (inSt (hp.stW uc₃.wr) (off := 72) (n := 4) (by decide)) fun s₄ u₄ => ?_
  refine wp_cmp (op2_imm (by decide)) fun s₅ u₅ hz => WP.block_nil ?_
  have uc₅ : UC s₀ s₅ := (uc₃.upd u₄ (by decide)).flags u₅
  have m₅ : s₅.mem = s₃.mem := by rw [u₅.mem, u₄.mem]
  have m₁ : s₁.mem = s.mem := u₁.mem
  -- The stored words.
  have st₂ : ∀ x ∈ wsList, ∀ d, x.2.1 = d → x.2.2 = false →
      s₅.mem.readW (stB s₀ + BitVec.ofNat 64 d) 32 = s₁.gpr x.1 := by
    intro x hx d hd hb
    have := hs₂ x hx
    obtain ⟨r, o, b⟩ := x
    simp only at hd hb; subst hd hb
    have hl : 20 ≤ o ∧ (124 ≤ o ∨ o + 4 ≤ 88) ∧ o < 128 := by
      have : ∀ x ∈ wsList, 20 ≤ x.2.1 ∧ (124 ≤ x.2.1 ∨ x.2.1 + 4 ≤ 88) ∧ x.2.1 < 128 := by decide
      exact this _ hx
    rw [m₅, k₃.frame.readW (Region.contains_self _ _) (dj_offR _ (d := o) (n := 4) (by
      simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq]; omega_using [hl])
      (by omega_using [hl]) (by decide)) (by decide)]
    exact this
  -- The key and the accumulator on entry.
  have hw₁ : ∀ d, (d + 4 ≤ 56 ∨ 72 ≤ d ∧ d + 4 ≤ 128) →
      s₁.mem.readW (stB s₀ + BitVec.ofNat 64 d) 32 = s₀.mem.readW (stB s₀ + BitVec.ofNat 64 d) 32 :=
    fun d hd => by rw [m₁]; exact sfr_word hp h.sfr hd
  have hRl : rlimb s₂.mem (stB s₀) = Rl s₀ := by
    rw [rlimb_frame' f₂ (by decide) (by decide), rlimb_frame fun i hi => hw₁ _ (by omega_using [hi])]
  have hA : accD s₂.mem (stB s₀) = accD s₀.mem (stB s₀) := by
    rw [accD_frame f₂ (by decide) (by decide), accD_of_words fun i hi => hw₁ _ (by omega_using [hi])]
  refine ⟨uc₅, ⟨uc₅.r0, hp.stW uc₅.wr, fun k hk => ?_, accD s₀.mem (stB s₀), ⟨fun k hk => ?_, ?_⟩,
    fun k _ => by have := accD_lt s₀.mem (stB s₀) k; omega_using [this], by rw [Poly1305.absorbAll_nil]⟩,
    ?_, ?_, ?_, ?_, ?_⟩
  · rw [m₅, hr₃ k hk, hRl]
  · have := yr_ne k hk
    rw [u₅.gpr, u₄.other _ this.2.1, ← hA]; exact hc₃.1 k hk
  · rw [m₅, ← hA]; exact hc₃.2
  · rw [st₂ _ (by decide : (Reg.r5, 124, false) ∈ wsList) 124 rfl rfl, u₁.other _ (by decide), h.r5]
  · rw [st₂ _ (by decide : (Reg.r6, 76, false) ∈ wsList) 76 rfl rfl, u₁.other _ (by decide), h.r6]
  · rw [st₂ _ (by decide : (Reg.r1, 20, false) ∈ wsList) 20 rfl rfl, e1]
  · rw [m₅, bytesAt_frame (p := stB s₀ + 56) k₃.frame (fun r hr => ((dj_offR _ (d := 56) (n := 16) (by decide) (by decide)
      (by decide) r hr).sub_left (Region.sub_prefix hn2))) (by omega_using [hn2]),
      bytesAt_frame (p := stB s₀ + 56) f₂ (fun r hr => ((dj_offR _ (d := 56) (n := 16) (by decide) (by decide)
      (by decide) r hr).sub_left (Region.sub_prefix hn2))) (by omega_using [hn2]), m₁]
    exact h.buf
  · have e72 := st₂ _ (by decide : (Reg.r4, 72, false) ∈ wsList) 72 rfl rfl
    rw [hz, u₄.gpr, ← m₅, e72, u₁.other _ (by decide), h.r4, show (16 : BitVec 32) = BitVec.ofNat 32 16 from rfl,
      sub_beq32 (by omega_using [hn2]) (by decide)]

/-! ## Absorbing the buffer -/

theorem X1_length (s₀ : State) : (X1 s₀).length % 16 = 0 := by
  simp only [X1]
  split
  · rename_i h
    simp only [List.length_append, Poly1305.length_bytesAt]; omega_using [h]
  · rfl

/-- The buffer absorbed, or not. -/
structure F4 (s₀ s : State) : Prop extends UC s₀ s where
  acc : Acc (s₀.gpr .r0) (Rl s₀) (A0 s₀) (X1 s₀) s
  ptr : s.mem.readW (stB s₀ + BitVec.ofNat 64 124) 32 = dp s₀ + BitVec.ofNat 32 (nf s₀)
  len : s.mem.readW (stB s₀ + BitVec.ofNat 64 76) 32 = BitVec.ofNat 32 (dl s₀ - nf s₀)
  cnt : s.mem.readW (stB s₀ + BitVec.ofNat 64 20) 32 = BitVec.ofNat 32 (nw s₀)
  buf : bytesAt s.mem (stB s₀ + 56) (kb s₀ + nf s₀) = Bf s₀ ++ Dt s₀ (nf s₀)

theorem buf_ok {s₀ : State} (hp : UPre s₀) {s : State} (h : F3 s₀ s) :
    WP isa (.ite .eq (.block (.dp .add .r1 .r0 (.imm 56) :: absorb true)) (.block [])) s (F4 s₀) := by
  have hfit := hp.st_fit
  obtain ⟨hn1, hn2, -, -⟩ := nf_facts s₀
  refine WP.ite s.z (eval_eq _) (fun hb => ?_) (fun hb => WP.block_nil ?_)
  · have h16 : kb s₀ + nf s₀ = 16 := by rw [h.z] at hb; simpa using hb
    refine wp_add (op2_imm (by decide)) fun s₁ u₁ => ?_
    have hA₁ : Acc (s₀.gpr .r0) (Rl s₀) (A0 s₀) [] s₁ :=
      h.acc.keep ((u₁.keeps (ws := [.r1]) (by simp)).keepsF (offR (stB s₀) [])) (by decide) (by decide)
        (by decide)
    have hr1 : s₁.gpr .r1 = s₀.gpr .r0 + 56 := by rw [u₁.gpr, h.r0]
    refine WP.mono (absorbAcc_ok hfit (fun i _ => rlimb_lt _ _ i) rfl hA₁ (a := stB s₀ + BitVec.ofNat 64 56)
      (fun j hj => by
        rw [hr1, BitVec.add_assoc, show (56 : BitVec 32) = BitVec.ofNat 32 56 from rfl, ← BitVec.ofNat_add,
          ea hfit (by omega_using [hj]), off_add])
      (fun j hj => by rw [off_add, u₁.rd, u₁.wr]; exact inSt (hp.stW h.wr) (by omega_using [hj])))
      fun s₂ ⟨hA₂, k₂⟩ => ?_
    have f₂ : Frame (offR (stB s₀) [(0, 20)]) s₁.mem s₂.mem := by rw [← accR_offR]; exact k₂.frame
    have k₂' : KeepsF work (offR (stB s₀) [(0, 20)]) s₁ s₂ := ⟨k₂.gpr, f₂, k₂.rd, k₂.wr, k₂.sp⟩
    have hbuf : bytesAt s₁.mem (stB s₀ + BitVec.ofNat 64 56) 16 = X1 s₀ := by
      rw [u₁.mem, X1, iteT h16, ← h.buf, h16]; rfl
    refine ⟨(h.toUC.upd u₁ (by decide)).keepsF hp k₂' (by decide) (by decide) (by decide), ?_, ?_, ?_, ?_, ?_⟩
    · rw [List.nil_append, hbuf] at hA₂; exact hA₂
    · rw [f₂.word (by decide) (by decide) (by decide), u₁.mem]; exact h.ptr
    · rw [f₂.word (by decide) (by decide) (by decide), u₁.mem]; exact h.len
    · rw [f₂.word (by decide) (by decide) (by decide), u₁.mem]; exact h.cnt
    · rw [bytesAt_frame (p := stB s₀ + 56) f₂ (fun r hr => ((dj_offR _ (d := 56) (n := 16) (by decide)
        (by decide) (by decide) r hr).sub_left (Region.sub_prefix hn2))) (by omega_using [h16]), u₁.mem]
      exact h.buf
  · have h16 : ¬ kb s₀ + nf s₀ = 16 := by rw [h.z] at hb; simpa using hb
    refine ⟨h.toUC, ?_, h.ptr, h.len, h.cnt, h.buf⟩
    rw [X1, iteF h16]; exact h.acc

/-! ## The whole blocks of the data -/

/-- Before whole block `i` of the rest of the data. -/
structure LI (s₀ : State) (i : Nat) (s : State) : Prop extends UC s₀ s where
  acc : Acc (s₀.gpr .r0) (Rl s₀) (A0 s₀) (X1 s₀ ++ Dd s₀ (nf s₀) (16 * i)) s
  ptr : s.mem.readW (stB s₀ + BitVec.ofNat 64 124) 32 = dp s₀ + BitVec.ofNat 32 (nf s₀ + 16 * i)
  len : s.mem.readW (stB s₀ + BitVec.ofNat 64 76) 32 = BitVec.ofNat 32 (dl s₀ - nf s₀)
  cnt : s.mem.readW (stB s₀ + BitVec.ofNat 64 20) 32 = BitVec.ofNat 32 (nw s₀ - i)
  buf : bytesAt s.mem (stB s₀ + 56) (kb s₀ + nf s₀) = Bf s₀ ++ Dt s₀ (nf s₀)

theorem LI.zero {s₀ s : State} (h : F4 s₀ s) : LI s₀ 0 s :=
  ⟨h.toUC, by simpa [Dd, bytesAt] using h.acc, by simpa using h.ptr, h.len, by simpa using h.cnt, h.buf⟩

theorem body_ok {s₀ : State} (hp : UPre s₀) {i : Nat} (hi : i < nw s₀) {s : State} (h : LI s₀ i s) :
    WP isa body s fun s' =>
      (isa.eval .ne s' = some false ∧ LI s₀ (nw s₀) s') ∨
      (isa.eval .ne s' = some true ∧ i + 1 < nw s₀ ∧ LI s₀ (i + 1) s') := by
  have hfit := hp.st_fit
  have hdf := hp.d_fit
  obtain ⟨hn1, hn2, -, -⟩ := nf_facts s₀
  have hdl := dl_lt s₀
  have hnw : 16 * nw s₀ ≤ dl s₀ - nf s₀ := by simp only [nw]; omega_using []
  have hpA : State.addr (dp s₀ + BitVec.ofNat 32 (nf s₀ + 16 * i)) = dA s₀ + BitVec.ofNat 64 (nf s₀ + 16 * i) :=
    addr_add (by omega_using [hi, hdf, hn1, hnw])
  have hblk : bytesAt s.mem (State.addr (dp s₀ + BitVec.ofNat 32 (nf s₀ + 16 * i))) 16 =
      bytesAt s₀.mem (dA s₀ + BitVec.ofNat 64 (nf s₀) + BitVec.ofNat 64 (16 * i)) 16 := by
    rw [hpA, off_add]
    simp only [bytesAt]
    apply List.map_congr_left
    intro j hj
    have hj := List.mem_range.mp hj
    rw [off_add]
    exact h.data hp (i := nf s₀ + 16 * i + j) (by omega_using [hi, hn1, hnw, hj])
  have hle : nf s₀ + 16 * i + 16 ≤ dl s₀ := by omega_using [hi, hn1, hnw]
  have hd : (⟨State.addr (dp s₀ + BitVec.ofNat 32 (nf s₀ + 16 * i)), 16⟩ : Region).Disjoint
      ⟨stB s₀ + BitVec.ofNat 64 124, 4⟩ := by
    rw [hpA]
    exact disjoint_of_sub hp.d_st (sub_base _ (len' := dl s₀) hle (by omega_using [hdl]))
      (sub_base _ (a := 124) (len := 4) (len' := 128) (by decide) (by decide))
  have hnw32 : nw s₀ < 2 ^ 32 := by simp only [nw]; omega_using [hn1, hdl, hle]
  refine WP.mono (body_gen hfit (fun i _ => rlimb_lt _ _ i) (by
      simp only [List.length_append, Poly1305.length_bytesAt]; have := X1_length s₀; omega_using [this]) h.acc h.ptr h.cnt
      (by omega_using [hi]) (by omega_using [hi, hnw32]) (by rw [toNat_add_ofNat (by omega_using [hdf, hle])]; omega_using [hdf, hle])
      (fun j hj => by
        rw [hpA, off_add, h.rd, hp.rd]
        exact ⟨_, List.mem_append_left _ List.mem_cons_self,
          contains_off (off := nf s₀ + 16 * i + 4 * j) (len := dl s₀) (by omega_using [hle, hj]) (by omega_using [hdl, hle, hj])⟩) hd)
    fun s' ⟨hA', k', hptr, hcnt, hz⟩ => ?_
  have hLI : LI s₀ (i + 1) s' := by
    refine ⟨h.toUC.keepsF hp k' (by decide) (by decide) (by decide), ?_, ?_, ?_, ?_, ?_⟩
    · rw [hblk, List.append_assoc, ← Poly1305.bytesAt_add, show 16 * i + 16 = 16 * (i + 1) by omega_using []] at hA'
      exact hA'
    · rw [hptr, BitVec.add_assoc, show (16 : BitVec 32) = BitVec.ofNat 32 16 from rfl, ← BitVec.ofNat_add]
      rfl
    · rw [k'.frame.word (by decide) (by decide) (by decide)]; exact h.len
    · rw [hcnt, Nat.sub_sub]
    · rw [bytesAt_frame (p := stB s₀ + 56) k'.frame (fun r hr => ((dj_offR _ (d := 56) (n := 16) (by decide)
        (by decide) (by decide) r hr).sub_left (Region.sub_prefix hn2))) (by omega_using [hn2])]
      exact h.buf
  by_cases hlast : i + 1 = nw s₀
  · exact .inl ⟨by rw [eval_ne, hz]; simp; omega_using [hlast], hlast ▸ hLI⟩
  · exact .inr ⟨by rw [eval_ne, hz]; simp; omega_using [hi, hlast], by omega_using [hi, hlast], hLI⟩

theorem head_ok {s₀ : State} (hp : UPre s₀) {s : State} (h : F4 s₀ s) :
    WP isa (.block [.ldr .r1 .r0 cntOff, .cmp .r1 (.imm 0)]) s fun s' =>
      LI s₀ 0 s' ∧ s'.z = decide (nw s₀ = 0) := by
  have hfit := hp.st_fit
  have hdl := dl_lt s₀
  have hnw : nw s₀ < 2 ^ 32 := by simp only [nw]; omega_using [hdl]
  refine wp_ldr (a := stB s₀ + BitVec.ofNat 64 20) (by decide) (by rw [h.r0]; exact ea hfit (off := 20) (by decide))
    (inSt (hp.stW h.wr) (off := 20) (n := 4) (by decide)) fun s₁ u₁ =>
      wp_cmp (op2_imm (by decide)) fun s₂ u₂ hz => WP.block_nil ⟨?_, ?_⟩
  · have h0 := LI.zero h
    exact ⟨(h0.toUC.upd u₁ (by decide)).flags u₂,
      h0.acc.keep (((u₁.keeps (ws := [.r1]) (by simp)).trans (u₂.keeps _)).keepsF (offR (stB s₀) []))
        (by decide) (by decide) (by decide),
      by rw [u₂.mem, u₁.mem]; exact h0.ptr, by rw [u₂.mem, u₁.mem]; exact h0.len,
      by rw [u₂.mem, u₁.mem]; exact h0.cnt, by rw [u₂.mem, u₁.mem]; exact h0.buf⟩
  · rw [hz, u₁.gpr, h.cnt, sub0, ofNat_beq_zero hnw]

theorem loop_ok {s₀ : State} (hp : UPre s₀) {s₂ : State} (hL : LI s₀ 0 s₂) (hz' : s₂.z = decide (nw s₀ = 0)) :
    WP isa (.ite .eq (.block []) (.loop body .ne)) s₂ (LI s₀ (nw s₀)) := by
  refine WP.ite s₂.z (eval_eq _) (fun hb => WP.block_nil ?_) (fun hb => ?_)
  · have h0 : nw s₀ = 0 := by rw [hz'] at hb; simpa using hb
    exact h0 ▸ hL
  · have hpos : 0 < nw s₀ := by rw [hz'] at hb; simp only [nw] at hb ⊢; simp at hb; omega_using [hb]
    refine WP.loop (M := isa) (fun m s => ∃ i, m = nw s₀ - i ∧ i < nw s₀ ∧ LI s₀ i s) ?_ (nw s₀) s₂
      ⟨0, rfl, hpos, hL⟩
    rintro m s ⟨i, rfl, hi, hLi⟩
    refine WP.mono (body_ok hp hi hLi) fun s' h' => ?_
    rcases h' with ⟨he, hc⟩ | ⟨he, hi', hL'⟩
    · exact .inl ⟨he, hc⟩
    · exact .inr ⟨he, nw s₀ - (i + 1), by omega_using [hi'], i + 1, rfl, hi', hL'⟩

/-! ## Storing the accumulator -/

/-- The key is unchanged. -/
theorem UC.key {s₀ : State} (hp : UPre s₀) {s : State} (h : UC s₀ s) :
    bytesAt s.mem (stB s₀ + 24) 32 = bytesAt s₀.mem (stB s₀ + 24) 32 :=
  bytesAt_frame (p := stB s₀ + BitVec.ofNat 64 24) h.frame (fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · exact dj_offR _ (d := 24) (n := 32) (by decide) (by decide) (by decide) r hr
    · simp only [List.mem_singleton] at hr; subst hr; exact hp.st_scr' (by decide)) (by decide)

/-- The whole blocks absorbed after the message's, and the bytes left. -/
abbrev Wb (s₀ : State) : List Byte := X1 s₀ ++ Dd s₀ (nf s₀) (16 * nw s₀)
abbrev Rst (s₀ : State) : List Byte := Dd s₀ (nf s₀ + 16 * nw s₀) (nr s₀)

/-- After storing the accumulator. -/
structure F6 (s₀ s : State) : Prop extends UC s₀ s where
  accv : leNum (bytesAt s.mem (stB s₀) 24) = Poly1305.absorbAll (Rn s₀) (A0 s₀) (Wb s₀) % P
  buf : bytesAt s.mem (stB s₀ + 56) (kb s₀ + nf s₀) = Bf s₀ ++ Dt s₀ (nf s₀)
  r8 : s.gpr .r8 = BitVec.ofNat 32 (nr s₀)
  r5 : s.gpr .r5 = dp s₀ + BitVec.ofNat 32 (nf s₀ + 16 * nw s₀)
  r1 : s.gpr .r1 = s₀.gpr .r0
  z : s.z = decide (nr s₀ = 0)

theorem epi_ok {s₀ : State} (hp : UPre s₀) {s : State} (h : LI s₀ (nw s₀) s) :
    WP isa (.block (reduce ++ toWords ++ storeAcc ++ ([.ldr .r8 .r0 lenOff, .dp .and .r8 .r8 (.imm 15),
      .ldr .r5 .r0 ptrOff, .mov .r1 (.reg .r0), .cmp .r8 (.imm 0)] : List Instr))) s (F6 s₀) := by
  have hfit := hp.st_fit
  obtain ⟨hn1, hn2, -, -⟩ := nf_facts s₀
  have hdl := dl_lt s₀
  have hnr : nr s₀ < 16 := Nat.mod_lt _ (by decide)
  rw [List.append_assoc, List.append_assoc, ← List.append_assoc toWords, ← List.append_assoc reduce]
  refine WP.append (storeAcc_ok hfit h.acc) fun s₁ ⟨hv₁, k₁⟩ => ?_
  have uc₁ : UC s₀ s₁ := h.toUC.keepsF hp k₁ (by decide) (by decide) (by decide)
  have hw₁ := hp.stW uc₁.wr
  refine wp_ldr (a := stB s₀ + BitVec.ofNat 64 76) (by decide) (by rw [uc₁.r0]; exact ea hfit (off := 76) (by decide))
    (inSt hw₁ (off := 76) (n := 4) (by decide)) fun s₂ u₂ => ?_
  refine wp_and (op2_imm (by decide)) fun s₃ u₃ => ?_
  refine wp_ldr (a := stB s₀ + BitVec.ofNat 64 124) (by decide)
    (by rw [u₃.other _ (by decide), u₂.other _ (by decide), uc₁.r0]; exact ea hfit (off := 124) (by decide))
    (by rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr]; exact inSt hw₁ (off := 124) (n := 4) (by decide)) fun s₄ u₄ => ?_
  refine wp_mov (op2_reg _ _) fun s₅ u₅ => wp_cmp (op2_imm (by decide)) fun s₆ u₆ hz => WP.block_nil ?_
  have m₆ : s₆.mem = s₁.mem := by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem]
  have e8 : s₅.gpr .r8 = BitVec.ofNat 32 (nr s₀) := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.gpr, k₁.frame.word (by decide) (by decide)
      (by decide), h.len, and15, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := dl s₀ - nf s₀) (by omega_using [hn1, hdl])]
  refine ⟨((((uc₁.upd u₂ (by decide)).upd u₃ (by decide)).upd u₄ (by decide)).upd u₅ (by decide)).flags u₆,
    by rw [m₆]; exact hv₁, ?_, by rw [u₆.gpr, e8], ?_, ?_, ?_⟩
  · rw [m₆, bytesAt_frame (p := stB s₀ + 56) k₁.frame (fun r hr => ((dj_offR _ (d := 56) (n := 16) (by decide)
      (by decide) (by decide) r hr).sub_left (Region.sub_prefix hn2))) (by omega_using [hn2])]
    exact h.buf
  · rw [u₆.gpr, u₅.other _ (by decide), u₄.gpr, u₃.mem, u₂.mem, k₁.frame.word (by decide) (by decide) (by decide),
      h.ptr]
  · rw [u₆.gpr, u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), uc₁.r0]
  · rw [hz, e8, sub0, ofNat_beq_zero (by omega_using [hnr])]

/-! ## The bytes left -/

/-- After copying the bytes left into the buffer. -/
structure F7 (s₀ s : State) : Prop extends UC s₀ s where
  accv : leNum (bytesAt s.mem (stB s₀) 24) = Poly1305.absorbAll (Rn s₀) (A0 s₀) (Wb s₀) % P
  buf : bytesAt s.mem (stB s₀ + 56) (Y0 s₀ ++ Rst s₀).length = Y0 s₀ ++ Rst s₀

theorem Y0_length (s₀ : State) : (Y0 s₀).length = if kb s₀ + nf s₀ = 16 then 0 else kb s₀ + nf s₀ := by
  simp only [Y0]
  split
  · rfl
  · simp only [List.length_append, Poly1305.length_bytesAt]

theorem rest_ok {s₀ : State} (hp : UPre s₀) {s : State} (h : F6 s₀ s) :
    WP isa (.ite .eq (.block []) copyIn) s (F7 s₀) := by
  have hfit := hp.st_fit
  have hdf := hp.d_fit
  obtain ⟨hn1, hn2, hn3, hn4⟩ := nf_facts s₀
  have hdl := dl_lt s₀
  have hlR : (Rst s₀).length = nr s₀ := Poly1305.length_bytesAt _ _ _
  have hdiv : nf s₀ + 16 * nw s₀ + nr s₀ = dl s₀ := by simp only [nw, nr]; omega_using [hn1]
  have hnr : nr s₀ < 16 := Nat.mod_lt _ (by decide)
  refine WP.ite s.z (eval_eq _) (fun hb => WP.block_nil ?_) (fun hb => ?_)
  · have h0 : nr s₀ = 0 := by rw [h.z] at hb; simpa using hb
    have hR : Rst s₀ = [] := List.eq_nil_of_length_eq_zero (by rw [hlR, h0])
    refine ⟨h.toUC, h.accv, ?_⟩
    rw [hR, List.append_nil, Y0_length]
    split
    · rename_i h16; simp [Y0, h16, bytesAt]
    · rename_i h16; rw [h.buf, Y0, iteF h16]
  · have hpos : 0 < nr s₀ := by rw [h.z] at hb; simp at hb; omega_using [hlR, hnr, hb]
    have hY : Y0 s₀ = [] := by
      simp only [Y0]
      split
      · rfl
      · rename_i h16
        rcases Nat.eq_zero_or_pos (kb s₀) with hk | hk
        · simp [Bf, Dt, hk, hn3 hk, bytesAt]
        · have := hn4 hk (by omega_using [hn2, h16]); simp only [nr] at hpos; omega_using [hn2, hdiv, hpos, h16, this]
    have hsA : ∀ i < nr s₀, State.addr (dp s₀ + BitVec.ofNat 32 (nf s₀ + 16 * nw s₀)) + BitVec.ofNat 64 i =
        dA s₀ + BitVec.ofNat 64 (nf s₀ + 16 * nw s₀ + i) := fun i hi => by
      rw [addr_add (by omega_using [hdf, hlR, hdiv, hnr, hpos]), off_add]
    have hS : SrcOk s (stB s₀) (dp s₀ + BitVec.ofNat 32 (nf s₀ + 16 * nw s₀)) (Rst s₀) := by
      intro i hi
      rw [hlR] at hi
      rw [hsA i hi]
      refine ⟨?_, fun hc => ?_, ?_⟩
      · rw [h.rd, hp.rd]
        exact ⟨_, List.mem_append_left _ List.mem_cons_self,
          contains_off (off := nf s₀ + 16 * nw s₀ + i) (len := dl s₀) (by omega_using [hdiv, hi]) (by omega_using [hdl, hdiv, hi])⟩
      · exact hp.d_st _ (contains_off (off := nf s₀ + 16 * nw s₀ + i) (len := dl s₀) (by omega_using [hdiv, hi]) (by omega_using [hdl, hdiv, hi]))
          (sub_base _ (by decide) (by decide) _ hc)
      · rw [h.data hp (by omega_using [hdiv, hi])]
        simp only [Rst, Dd, bytesAt, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi,
          Option.map_some, Option.getD_some, off_add]
    refine WP.mono (copy_ok hfit (sI := s) (j0 := 0) (by rw [hlR]; omega_using [hlR, hnr, hpos])
      (by rw [hlR, toNat_add_ofNat (by omega_using [hdf, hlR, hdiv, hnr, hpos])]; omega_using [hdf, hdiv])
      (by rw [hlR]; omega_using [hpos]) (hp.stW h.wr) hS h.r5 (by rw [h.r1]; simp) (by rw [h.r8, hlR])) fun s₁ hc => ?_
    have k₁ := CopyInv.keepsF (by rw [hlR]; omega_using [hlR, hnr, hpos]) hc
    have hd0 : ∀ r ∈ offR (stB s₀) [(56, 16)], (⟨stB s₀, 24⟩ : Region).Disjoint r := fun r hr => by
      have := dj_offR _ (d := 0) (n := 24) (by decide) (by decide) (by decide) r hr
      simpa using this
    refine ⟨h.toUC.keepsF hp k₁ (by decide) (by decide) (by decide), ?_, ?_⟩
    · rw [bytesAt_frame k₁.frame hd0 (by decide)]
      exact h.accv
    · rw [hY, List.nil_append]
      have := CopyInv.buf (j0 := 0) (by rw [hlR]; omega_using [hlR, hnr, hpos]) hc
      rw [Nat.zero_add] at this
      rw [this]
      simp [bytesAt]

/-! ## The whole function -/

theorem cnt_mod (s₀ : State) : (Proof.Poly1305.countArm s₀).toNat % 16 = kb s₀ := by
  simp only [kb, Proof.Poly1305.countArm]
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt (s₀.gpr .r2).isLt, Nat.shiftLeft_eq]
  omega_using []

theorem restore_ok {s₀ : State} (hp : UPre s₀) {s : State} (h : F7 s₀ s) :
    WP isa (.block (.ldrSp .r12 8 :: restoreScr)) s fun s' =>
      abiPreserved s₀ s' ∧ Proof.Poly1305.updateArm.post s₀ s' := by
  refine wp_arg (i := 2) hp h.toUC (by decide) fun s₁ u₁ => ?_
  refine WP.mono (restoreScr_ok (g := s₀.gpr) hp.sc_fit u₁.gpr (by rw [u₁.wr]; exact hp.scW h.wr)
    (by rw [u₁.mem]; exact h.saved)) fun s' ⟨hr', k'⟩ => ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · rcases preserved_cases r hr with rfl | ⟨i, hi, rfl⟩
    · rw [k'.gpr _ (by decide), u₁.other _ (by decide), h.lr]
    · exact hr' i hi
  · rw [k'.sp, u₁.sp, h.sp]
  intro key msg hbuf hcnt
  obtain ⟨hn1, hn2, hn3, hn4⟩ := nf_facts s₀
  have m' : s'.mem = s.mem := by rw [k'.mem, u₁.mem]
  obtain ⟨w, b, rfl, hrep, hbl, hbb⟩ := Proof.Poly1305.Buffered.split hbuf
  have hkb : (w ++ b).length % 16 = kb s₀ := by
    rw [← cnt_mod, hcnt, BitVec.toNat_ofNat]; omega_using [hbl]
  have hb : b = Bf s₀ := by rw [← hbb, hkb]
  subst hb
  obtain ⟨hlen, hkey, hacc⟩ := hrep
  -- The data, split.
  have hdiv : nf s₀ + 16 * nw s₀ + nr s₀ = dl s₀ := by simp only [nw, nr]; omega_using [hn1]
  have hD : bytesAt s₀.mem (State.addr (stackArg s₀ 0)) (stackArg s₀ 1).toNat =
      Dt s₀ (nf s₀) ++ Dd s₀ (nf s₀) (16 * nw s₀) ++ Rst s₀ := by
    rw [show (stackArg s₀ 1).toNat = nf s₀ + 16 * nw s₀ + nr s₀ from hdiv.symm, Poly1305.bytesAt_add,
      Poly1305.bytesAt_add]
  have hsplit : Bf s₀ ++ (Dt s₀ (nf s₀) ++ Dd s₀ (nf s₀) (16 * nw s₀) ++ Rst s₀) = Wb s₀ ++ (Y0 s₀ ++ Rst s₀) := by
    simp only [Wb, X1, Y0]
    split
    · simp only [List.append_assoc, List.nil_append]
    · rename_i h16
      rcases Nat.eq_zero_or_pos (kb s₀) with hk | hk
      · simp [Bf, Dt, hk, hn3 hk, bytesAt]
      · have hnd := hn4 hk (by omega_using [hn2, hkb, h16])
        have hw0 : nw s₀ = 0 := by simp only [nw]; omega_using [hdiv, hnd]
        have hr0 : nr s₀ = 0 := by simp only [nr]; omega_using [hdiv, hnd]
        simp [Rst, Dd, hw0, hr0, bytesAt]
  have hWl : (Wb s₀).length % 16 = 0 := by
    simp only [Wb, List.length_append, Poly1305.length_bytesAt]; have := X1_length s₀; omega_using [this]
  have hYl : (Y0 s₀ ++ Rst s₀).length < 16 := by
    rw [List.length_append, Y0_length, Poly1305.length_bytesAt]
    split
    · simp only [nr]; omega_using []
    · rename_i h16
      rcases Nat.eq_zero_or_pos (kb s₀) with hk | hk
      · rw [hk, hn3 hk]; simp only [nr]; omega_using []
      · have hnd := hn4 hk (by omega_using [hn2, hkb, h16])
        have : nr s₀ = 0 := by simp only [nr]; omega_using [hdiv, hnd]
        omega_using [hn2, hkb, hdiv, h16, hnd, this]
  rw [hD, List.append_assoc, hsplit, ← List.append_assoc]
  refine Buffered.of ⟨?_, ?_, ?_⟩ hYl (by rw [m']; exact h.buf)
  · rw [List.length_append]; omega_using [hlen, hWl]
  · rw [m', h.key hp]; exact hkey
  · rw [m', h.accv]
    rw [← hkey, take_bytesAt _ _ (by decide), ← val_rlimb] at hacc ⊢
    rw [Poly1305.accumulate_append hlen]
    have hlt : leNum (bytesAt s₀.mem (stB s₀) 24) < P := by rw [hacc]; exact Poly1305.accumulate_lt _ _
    have hA : accumulate (Rn s₀) w = A0 s₀ := by rw [A0, val_accD_eq hlt]; exact hacc.symm
    rw [hA, Nat.mod_eq_of_lt (Poly1305.absorbAll_lt (by rw [← hA]; exact Poly1305.accumulate_lt _ _) _)]

theorem update_correct {s₀ : State} (hp : UPre s₀) :
    WP isa update s₀ fun s' => abiPreserved s₀ s' ∧ Proof.Poly1305.updateArm.post s₀ s' := by
  refine WP.seq (WP.mono (prologue_ok hp) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (fill_ok hp h₁) fun s₂ h₂ => ?_)
  refine WP.seq (WP.mono (mid_ok hp h₂) fun s₃ h₃ => ?_)
  refine WP.seq (WP.mono (buf_ok hp h₃) fun s₄ h₄ => ?_)
  refine WP.seq (WP.mono (head_ok hp h₄) fun s₄' ⟨hL, hz⟩ => ?_)
  refine WP.seq (WP.mono (loop_ok hp hL hz) fun s₅ h₅ => ?_)
  refine WP.seq (WP.mono (epi_ok hp h₅) fun s₆ h₆ => ?_)
  exact WP.seq (WP.mono (rest_ok hp h₆) fun s₇ h₇ => restore_ok hp h₇)

/-! ## Constant time -/

/-- The initial taint: `r0` (`state`) and `r2:r3` (`count`) are public, `r0`
points at the state, and the 12 bytes of stack arguments are public, the
third one pointing at `scratch`. The analysis tracks the public slots of the
state (the working space). -/
def τu : VG.Arm.Taint.T :=
  { regs := .ofList [.r0, .r2, .r3], flags := false, lens := [128, 128], bases := [(.r0, 0)], argLen := 12,
    argBases := [(8, 1)] }

theorem argByte_eq {s : State} (hsp : s.sp.toNat + 12 ≤ 2 ^ 32) {k : Nat} (hk : k < 12) :
    VG.Arm.Taint.argByte s k = stackArgAddr s (k / 4) + BitVec.ofNat 64 (k % 4) := by
  simp only [VG.Arm.Taint.argByte, stackArgAddr]
  rw [addr_add (by omega_using [hsp, hk]), BitVec.add_assoc, ← BitVec.ofNat_add]
  congr 2; omega_using []

theorem wfu {s : State} (h : Proof.Poly1305.updateArm.pre s) : VG.Arm.Taint.Wf τu s := by
  have hp := UPre.of s h
  have hst := hp.st_fit; have hsc := hp.sc_fit; have hs := hp.sp_fit
  refine ⟨fun _ => ⟨by simp [hp.wr, τu], by simpa [hp.wr] using hp.st_scr, ?_⟩, ?_, fun _ => ⟨hs, ?_⟩, ?_⟩
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only [addr_toNat] <;> omega_using [hst, hsc]
  · intro p hp'; simp only [τu, List.mem_singleton] at hp'; subst hp'; simp [VG.Arm.Taint.region, hp.wr]
  · have e : (⟨State.addr s.sp, 12⟩ : Region) = argR s := by simp [stackArgAddr]
    simp only [τu, e, hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact hp.a_st
    · exact hp.a_scr
  · intro p hp'; simp only [τu, List.mem_singleton] at hp'; subst hp'
    refine ⟨by decide, ?_⟩
    simp only [VG.Arm.Taint.region, hp.wr]
    rfl

theorem agreeu {s₁ s₂ : State} (h₁ : Proof.Poly1305.updateArm.pre s₁) (h₂ : Proof.Poly1305.updateArm.pre s₂)
    (hpub : Proof.Poly1305.updateArm.pub s₁ s₂) : VG.Arm.Taint.Agree τu s₁ s₂ := by
  obtain ⟨psp, p0, p2, p3, a0, a1, a2⟩ := hpub
  have hp₁ := UPre.of s₁ h₁; have hp₂ := UPre.of s₂ h₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, wfu h₁, wfu h₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun _ => psp, fun k hk => ?_⟩
  · simp only [τu, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> assumption
  · rw [hp₁.wr, hp₂.wr]; simp only [stR, scrR, sc, p0, a2]
  · simp only [τu] at hk
    rw [argByte_eq hp₁.sp_fit hk, argByte_eq hp₂.sp_fit hk, Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by decide)),
      Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by decide))]
    have : k / 4 = 0 ∨ k / 4 = 1 ∨ k / 4 = 2 := by omega_using [hk]
    rcases this with h | h | h <;> rw [h]
    · exact congrArg _ a0
    · exact congrArg _ a1
    · exact congrArg _ a2

/-- A state satisfying the precondition (with no data, and `scratch` at 0). -/
def updateSat : State where
  gpr r := match r with
    | .r0 => 0x1000 | _ => 0
  sp := 0x4000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0, 0⟩, ⟨0x4000, 12⟩]
  wr := [⟨0x1000, 128⟩, ⟨0, 128⟩]

theorem update_ok (s : State) (hs : Proof.Poly1305.updateArm.pre s) :
    ∃ t s', Exec isa update s t s' ∧ abiPreserved s s' ∧ Proof.Poly1305.updateArm.post s s' :=
  update_correct (UPre.of s hs)

theorem update_ct : ConstantTime isa Proof.Poly1305.updateArm.pre Proof.Poly1305.updateArm.pub
    update := by
  exact VG.Taint.constantTime (A := taint) τu (fun _ _ h₁ h₂ hp => agreeu h₁ h₂ hp) (by
      taint_decide)

theorem update_verified :
    Verified Arm.target Impl.Poly1305.Arm.update (Spec.Poly1305.updateContract Arm.abi) :=
  Verified.of_correct update_ok update_ct (by
    sig_implies [Spec.Poly1305.updateContract, Spec.Poly1305.updateSig, Proof.Poly1305.updateArm,
      Proof.Poly1305.countArm, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
      Arm.State.addr] [Proof.Poly1305.Arm.Update.updateSat, Arm.stackArg, Arm.stackArgAddr,
      Mem.readW, Mem.read] using Proof.Poly1305.Arm.Update.updateSat)

end VG.Proof.Poly1305.Arm.Update
