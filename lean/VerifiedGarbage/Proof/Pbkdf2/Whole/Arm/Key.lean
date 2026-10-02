import VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.Common
import VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.Upd

/-!
# PBKDF2-HMAC on 32-bit ARM, the whole derivation: the prologue and the key

Untrusted: everything here is checked by Lean. As on x86
(`Proof/Pbkdf2/Whole/X86/Key.lean`): the prologue saves our caller's
registers in `scratch` (`save_ok`, `VG.Proof.Hmac.Generic.Arm.save_ok` for
any amount of working space before the save area that an immediate offset
reaches) and keeps the arguments in registers; then the key is the
password, or its digest if it is longer than a block (`key_ok`): either
gives the same `K₀`.
-/

namespace VG.Proof.Pbkdf2.Whole.Arm

open VG.Arm
open VG.Impl.Pbkdf2.Whole.Arm (Fns)
open VG.Impl.Hmac.Generic.Arm (Hash scrAt)
open VG.Proof.Hmac.Generic.Arm (HashOK SavedRegs saveR FinArgs init_call fin_frame count saveMem_frameR
  saveMem_read saved_mem saved_pairwise savedRegs)
open VG.Proof.MdStream.Arm (Upd Fupd wp_mov wp_ldrSp op2_imm op2_reg saveList_ok contains_offset eval_eq)
open VG.Proof.Hmac.Generic.Common (bytes_keep bytesAt_take)
open VG.Proof.Hmac.Common (bytesAt_length)
open Spec.Sha256 (bytesAt)
open Spec.Hmac (blockKey)

variable {F : Fns}

/-- Saving the registers, with `scratch` in `r12`: `VG.Proof.Hmac.Generic.Arm.save_ok`, for any
working space before the save area that an immediate offset reaches. -/
theorem save_ok (H : Hash) {s : State} {sc : BitVec 32} {L : Nat} (h12 : s.gpr .r12 = sc)
    (hW : 8 * H.W + 36 ≤ 4096) (hsc : ⟨State.addr sc, L⟩ ∈ s.wr) (hL : 8 * H.W + 36 ≤ L)
    (hfit : sc.toNat + L ≤ 2 ^ 32) {rest : List Instr} {Q : State → Prop}
    (k : ∀ s', s'.gpr = s.gpr → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      Frame [saveR H sc] s.mem s'.mem → SavedRegs H sc s s'.mem → WP isa (.block rest) s' Q) :
    WP isa (.block (H.save ++ rest)) s Q := by
  rw [Hmac.Generic.Arm.save_eq]
  refine saveList_ok H.saved s Q (fun p hp => ?_) fun s' g rd wr sp m => k s' g rd wr sp ?_ ?_
  · obtain ⟨h₁, h₂⟩ := saved_mem H hp
    rw [h12]
    exact ⟨by omega, by omega, ⟨_, hsc, contains_offset (by omega) (by omega)⟩⟩
  · rw [m, h12]
    exact saveMem_frameR _ _ _ _ (by omega) _ _ fun p hp => saved_mem H hp
  · intro p hp
    rw [m, h12]
    exact saveMem_read _ _ _ _ (saved_pairwise H) (fun q hq => by have := saved_mem H hq; omega) p hp

theorem zero_append (x : BitVec 32) : (0 : BitVec 32) ++ x = BitVec.ofNat 64 x.toNat := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_append, BitVec.toNat_ofNat]
  have := x.isLt
  simp only [show (0 : BitVec 32).toNat = 0 from rfl, Nat.zero_shiftLeft, Nat.zero_or]
  omega

theorem ofNat_toNat32 (x : BitVec 32) : BitVec.ofNat 32 x.toNat = x := by
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]

section
variable {s₀ : State} (hp : Pre F s₀) (hz : Sizes F)
include hp hz

/-! ## The prologue -/

/-- After the prologue: `KR`, and the password in `r8` and `r9`. -/
structure KK (F : Fns) (s₀ s : State) : Prop where
  kr : KR F s₀ s
  r8 : s.gpr .r8 = pw s₀
  r9 : s.gpr .r9 = s₀.gpr .r1

theorem prologue_ok : WP isa (.block F.prologue) s₀ (KK F s₀) := by
  have hL := end_le hz; have := layout (F := F); have hr := hz.reach
  have hsc := sc_mem hp
  simp only [Fns.prologue, List.cons_append]
  refine wp_ldrSp (a := stackArgAddr s₀ 3) (by decide) rfl (by
      rw [hp.rd, hp.wr]
      exact ⟨argR s₀, by simp, argR_sub hp (i := 3) (by decide) |> fun h => by
        have e : stackArgAddr s₀ 3 = State.addr s₀.sp + BitVec.ofNat 64 12 :=
          addr_add (by have := hp.spf; omega)
        have e0 : stackArgAddr s₀ 0 = State.addr s₀.sp := by simp [stackArgAddr]
        show Region.Contains ⟨stackArgAddr s₀ 0, 16⟩ _ 4
        rw [e, e0]; exact Offset.contains_base _ (by omega) (by omega)⟩) fun s₁ u₁ => ?_
  refine save_ok F.L (sc := scr s₀) (L := F.L8) u₁.gpr (by simp only [Fns.L]; omega) (by rw [u₁.wr]; exact hsc)
    (by show 8 * F.W + 36 ≤ F.L8; omega) hp.nsc fun s₂ g₂ rd₂ wr₂ sp₂ f₂ sv₂ => ?_
  refine wp_mov (op2_reg _ _) fun s₃ u₃ => wp_mov (op2_reg _ _) fun s₄ u₄ => wp_mov (op2_reg _ _) fun s₅ u₅ =>
    wp_mov (op2_reg _ _) fun s₆ u₆ => wp_mov (op2_reg _ _) fun s₇ u₇ => WP.block_nil ?_
  have e₂ : ∀ r, r ≠ .r12 → s₂.gpr r = s₀.gpr r := fun r hr => by rw [g₂, u₁.other r hr]
  refine ⟨⟨by rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, rd₂, u₁.rd], by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, wr₂, u₁.wr],
    by rw [u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, sp₂, u₁.sp], ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      e₂ _ (by decide)]
  · rw [u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      e₂ _ (by decide)]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr,
      g₂, u₁.gpr]; rfl
  · rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem]
    exact sv₂.of_eq F.L fun r hr => u₁.other r (by
      simp only [savedRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  · rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, ← u₁.mem]
    exact f₂.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨scR s₀ F, by simp, sv_sub hz⟩
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide),
      e₂ _ (by decide)]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide),
      e₂ _ (by decide)]

/-! ## The stack and `scratch`, while `KR` holds -/

omit hp hz in
theorem below_sub {s : State} (hk : KR F s₀ s) : Region.Sub (Hmac.Generic.Arm.below s) (stkR s₀) := by
  rw [← hk.stkE]; exact below_stk (n := 16) (by decide)

omit hz in
/-- A region of `scratch` is apart from the stack below the stack pointer. -/
theorem b24 {s : State} (hk : KR F s₀ s) {R : Region} (hR : Region.Sub R (scR s₀ F)) : (stk s).Disjoint R := by
  rw [hk.stkE]; exact hp.b_s.sub_right hR

omit hz in
theorem b16 {s : State} (hk : KR F s₀ s) {R : Region} (hR : Region.Sub R (scR s₀ F)) :
    (Hmac.Generic.Arm.below s).Disjoint R :=
  (hp.b_s.sub_left (below_sub hk)).sub_right hR

omit hz in
/-- A part of `scratch` is in a region the code may write. -/
theorem cov_part {s : State} (hk : KR F s₀ s) {o n : Nat} (h : o + n ≤ F.L8) :
    ∃ r' ∈ s.wr, ∃ off, (sR s₀ o n).base = r'.base + BitVec.ofNat 64 off ∧ off + (sR s₀ o n).len ≤ r'.len :=
  ⟨scR s₀ F, by rw [hk.wr]; exact sc_mem hp, o, rfl, h⟩

omit hz in
theorem cov_low {s : State} (hk : KR F s₀ s) {k : Nat} (h : k ≤ F.L8) :
    ∃ r' ∈ s.wr, ∃ off, (lowR s₀ k).base = r'.base + BitVec.ofNat 64 off ∧ off + (lowR s₀ k).len ≤ r'.len :=
  ⟨scR s₀ F, by rw [hk.wr]; exact sc_mem hp, 0, by simp, by simp only [Nat.zero_add]; exact h⟩

omit hz in
theorem cov_pw {s : State} (hk : KR F s₀ s) : Covers [pwR s₀] (s.rd ++ s.wr) :=
  Hmac.Generic.Arm.covers_one (List.mem_append_left _ (by rw [hk.rd, hp.rd]; simp))

omit hz in
theorem cov_salt {s : State} (hk : KR F s₀ s) : Covers [saltR s₀] (s.rd ++ s.wr) :=
  Hmac.Generic.Arm.covers_one (List.mem_append_left _ (by rw [hk.rd, hp.rd]; simp))

/-! ## Hashing a password longer than a block -/

variable (hH : HashOK F.H)
include hH

omit hp hz hH in
/-- `r4 ← scratch + stWO`. -/
theorem hk1_ok {s : State} (hk : KK F s₀ s) (ho : F.stWO < 2 ^ 16) :
    WP isa (.block (scrAt .r4 F.stWO)) s fun t => KK F s₀ t ∧ t.gpr .r4 = dO s₀ F.stWO ∧ t.mem = s.mem := by
  rw [← List.append_nil (scrAt .r4 F.stWO)]
  exact scr_ok hk.kr ho fun s₁ u₁ => WP.block_nil ⟨⟨hk.kr.upd12 (by decide) u₁,
    by rw [u₁.other _ (by decide) (by decide), hk.r8], by rw [u₁.other _ (by decide) (by decide), hk.r9]⟩, u₁.gpr, u₁.mem⟩

omit hp hz hH in
/-- `r0 ← r4`, before `init`. -/
theorem hk2a_ok {s : State} (hk : KK F s₀ s) (h4 : s.gpr .r4 = dO s₀ F.stWO) :
    WP isa (.block [.mov .r0 (.reg .r4)]) s fun t => KK F s₀ t ∧ t.gpr .r4 = dO s₀ F.stWO ∧
      t.gpr .r0 = dO s₀ F.stWO := by
  refine wp_mov (op2_reg _ _) fun s₁ u₁ => WP.block_nil ⟨⟨hk.kr.upd (by decide) u₁, ?_, ?_⟩, ?_, ?_⟩
  · rw [u₁.other _ (by decide), hk.r8]
  · rw [u₁.other _ (by decide), hk.r9]
  · rw [u₁.other _ (by decide), h4]
  · rw [u₁.gpr, h4]

/-- `init` on the working state. -/
theorem hk2b_ok {s : State} (hk : KK F s₀ s) (h4 : s.gpr .r4 = dO s₀ F.stWO) (h0 : s.gpr .r0 = dO s₀ F.stWO) :
    WP isa (.call F.H.initN F.H.initC) s fun t => KK F s₀ t ∧ hH.SH.Repr t.mem (A s₀ F.stWO) [] ∧
      t.gpr .r4 = dO s₀ F.stWO := by
  have hl := layout (F := F); have he := end_le hz; have := hz.S; have := hz.reach
  have ea := dO_addr hp (o := F.stWO) (by omega)
  have cw : Covers [⟨State.addr (dO s₀ F.stWO), F.H.S⟩] s.wr := by
    rw [ea]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr; exact cov_part hp hk.kr (by omega)
  refine init_call hH (st := dO s₀ F.stWO) h0 (by rw [dO_toNat hp (by omega)]; have := hp.nsc; omega)
    cw fun s' a r => ?_
  have a' := After.of_hmac a
  refine ⟨⟨hk.kr.call hp hz a' fun r hr => ?_, ?_, ?_⟩, by rw [← ea]; exact r, ?_⟩
  · simp only [List.mem_singleton] at hr; subst hr
    exact .inr ⟨_, _, by rw [ea], by omega, by omega⟩
  · rw [a.cs _ (by decide) (by decide), hk.r8]
  · rw [a.cs _ (by decide) (by decide), hk.r9]
  · rw [a.cs _ (by decide) (by decide), h4]

/-- `init` on the working state. -/
theorem hk2_ok {s : State} (hk : KK F s₀ s) (h4 : s.gpr .r4 = dO s₀ F.stWO) :
    WP isa (F.H.callInit .r4) s fun t => KK F s₀ t ∧ hH.SH.Repr t.mem (A s₀ F.stWO) [] ∧
      t.gpr .r4 = dO s₀ F.stWO := by
  unfold Hash.callInit
  exact WP.seq (WP.mono (hk2a_ok hk h4) fun s₁ ⟨k₁, d₁, a₁⟩ => hk2b_ok hp hz hH k₁ d₁ a₁)

omit hp hz hH in
/-- `update`'s arguments: the password. -/
theorem hk3_ok {s : State} (hk : KK F s₀ s) (h4 : s.gpr .r4 = dO s₀ F.stWO) :
    WP isa (.block [.mov .r0 (.reg .r4), .mov .r1 (.reg .r8), .mov .r7 (.reg .r9), .mov .r10 (.reg .r11),
      .mov .r2 (.imm 0), .mov .r3 (.imm 0)]) s fun t => KK F s₀ t ∧ t.gpr .r4 = dO s₀ F.stWO ∧
        t.gpr .r0 = dO s₀ F.stWO ∧ t.gpr .r1 = pw s₀ ∧ t.gpr .r7 = s₀.gpr .r1 ∧ t.gpr .r10 = scr s₀ ∧
        count t = BitVec.ofNat 64 0 ∧ t.mem = s.mem := by
  refine wp_mov (op2_reg _ _) fun s₁ u₁ => wp_mov (op2_reg _ _) fun s₂ u₂ => wp_mov (op2_reg _ _) fun s₃ u₃ =>
    wp_mov (op2_reg _ _) fun s₄ u₄ => wp_mov (op2_imm (by decide)) fun s₅ u₅ => wp_mov (op2_imm (by decide))
    fun s₆ u₆ => WP.block_nil ?_
  have k₆ := (((((hk.kr.upd (by decide) u₁).upd (by decide) u₂).upd (by decide) u₃).upd (by decide) u₄).upd
    (by decide) u₅).upd (by decide) u₆
  refine ⟨⟨k₆, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]⟩
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), hk.r8]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), hk.r9]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), h4]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.gpr, h4]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.gpr, u₁.other _ (by decide), hk.r8]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide),
      u₁.other _ (by decide), hk.r9]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), hk.kr.r11]
  · simp only [count]; rw [u₆.gpr, u₆.other .r2 (by decide), u₅.gpr]; rfl

theorem hk4_args {s : State} (hk : KK F s₀ s) (h0 : s.gpr .r0 = dO s₀ F.stWO) (h1 : s.gpr .r1 = pw s₀)
    (h7 : s.gpr .r7 = s₀.gpr .r1) (h10 : s.gpr .r10 = scr s₀) :
    UpdL hH s (dO s₀ F.stWO) (pw s₀) (scr s₀) (pwl s₀) := by
  have hl := layout (F := F); have he := end_le hz; have := hz.S; have := hz.D; have := hz.W; have := hz.reach
  have := hH.hWb
  have k := hk.kr
  have ea := dO_addr hp (o := F.stWO) (by omega)
  exact
    { r0 := h0
      r1 := h1
      r7 := by rw [h7, ofNat_toNat32]
      r10 := h10
      hlen := (s₀.gpr .r1).isLt
      sp16 := by rw [k.sp]; have := hp.sp24; omega
      cd := cov_pw hp k
      cw := by
        rw [ea]
        exact Covers.of_sub fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact cov_part hp k (by omega)
          · exact cov_low hp k (by omega)
      st_sc := by rw [ea]; exact (low_disj hz (k := hH.Wb) (by omega) (by omega)).symm
      d_st := by rw [ea]; exact hp.pw_s.sub_right (part_sub (by omega))
      d_sc := hp.pw_s.sub_right (low_sub (by omega))
      b_st := by rw [ea]; exact b16 hp k (part_sub (by omega))
      b_d := hp.b_pw.sub_left (below_sub k)
      b_sc := b16 hp k (low_sub (by omega))
      nst := by rw [dO_toNat hp (by omega)]; have := hp.nsc; omega
      nd := hp.npw
      nsc := by have := hp.nsc; omega }

theorem hk4_ok {s : State} (hk : KK F s₀ s) (h4 : s.gpr .r4 = dO s₀ F.stWO) (h0 : s.gpr .r0 = dO s₀ F.stWO)
    (h1 : s.gpr .r1 = pw s₀) (h7 : s.gpr .r7 = s₀.gpr .r1) (h10 : s.gpr .r10 = scr s₀)
    (hc : count s = BitVec.ofNat 64 0) (hr : hH.SH.Repr s.mem (A s₀ F.stWO) []) :
    WP isa (.frame (.push [.r1, .r7, .r10, .r12]) (.call F.H.updN F.H.updC) (.pop .r1 16)) s
      fun t => KK F s₀ t ∧ t.gpr .r4 = dO s₀ F.stWO ∧
        hH.SH.Repr t.mem (A s₀ F.stWO) (bytesAt s₀.mem (State.addr (pw s₀)) (pwl s₀)) := by
  have hl := layout (F := F); have he := end_le hz; have := hz.S; have := hz.D; have := hz.W; have := hz.reach
  have := hH.hWb
  have ea := dO_addr hp (o := F.stWO) (by omega)
  refine upd_frame hH (hk4_args hp hz hH hk h0 h1 h7 h10) fun s' a r => ⟨⟨hk.kr.call hp hz (After.of_hmac a)
    fun r hr => ?_, by rw [a.cs _ (by decide) (by decide), hk.r8], by rw [a.cs _ (by decide) (by decide), hk.r9]⟩,
    by rw [a.cs _ (by decide) (by decide), h4], ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact .inr ⟨_, _, by rw [ea], by omega, by omega⟩
    · exact .inl ⟨_, rfl, by omega⟩
  · have := r [] (by rw [ea]; exact hr) hc
    rwa [List.nil_append, ea, hk.kr.pwBytes hp] at this

omit hp hz hH in
/-- `finalize`'s arguments: the digest into `scratch`. -/
theorem hk5_ok {s : State} (hk : KK F s₀ s) (h4 : s.gpr .r4 = dO s₀ F.stWO) (ho : F.hkO < 2 ^ 16) :
    WP isa (.block ([.mov .r0 (.reg .r4)] ++ scrAt .r1 F.hkO ++ [.mov .r12 (.reg .r11), .mov .r2 (.reg .r9),
      .mov .r3 (.imm 0)])) s fun t => KK F s₀ t ∧ t.gpr .r0 = dO s₀ F.stWO ∧ t.gpr .r1 = dO s₀ F.hkO ∧
        t.gpr .r12 = scr s₀ ∧ count t = BitVec.ofNat 64 (pwl s₀) ∧ t.mem = s.mem := by
  simp only [List.cons_append, List.nil_append]
  refine wp_mov (op2_reg _ _) fun s₁ u₁ => ?_
  have k₁ := hk.kr.upd (by decide) u₁
  refine scr_ok k₁ ho fun s₂ u₂ => ?_
  have k₂ := k₁.upd12 (by decide) u₂
  refine wp_mov (op2_reg _ _) fun s₃ u₃ => wp_mov (op2_reg _ _) fun s₄ u₄ => wp_mov (op2_imm (by decide))
    fun s₅ u₅ => WP.block_nil ?_
  have k₅ := ((k₂.upd (by decide) u₃).upd (by decide) u₄).upd (by decide) u₅
  have e8 : s₂.gpr .r8 = pw s₀ := by rw [u₂.other _ (by decide) (by decide), u₁.other _ (by decide), hk.r8]
  have e9 : s₂.gpr .r9 = s₀.gpr .r1 := by rw [u₂.other _ (by decide) (by decide), u₁.other _ (by decide), hk.r9]
  refine ⟨⟨k₅, ?_, ?_⟩, ?_, ?_, ?_, ?_, by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]⟩
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), e8]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), e9]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide) (by decide),
      u₁.gpr, h4]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide) (by decide),
      u₁.other _ (by decide), hk.kr.r11]
  · simp only [count]; rw [u₅.gpr, u₅.other .r2 (by decide), u₄.gpr, u₃.other _ (by decide), e9, zero_append]

theorem hk6_args {s : State} (hk : KK F s₀ s) (h0 : s.gpr .r0 = dO s₀ F.stWO) (h1 : s.gpr .r1 = dO s₀ F.hkO)
    (h12 : s.gpr .r12 = scr s₀) : FinArgs hH s (dO s₀ F.stWO) (dO s₀ F.hkO) (scr s₀) := by
  have hl := layout (F := F); have he := end_le hz; have := hz.S; have := hz.D; have := hz.W; have := hz.reach
  have := hH.hWb
  have k := hk.kr
  have ea := dO_addr hp (o := F.stWO) (by omega)
  have eh := dO_addr hp (o := F.hkO) (by omega)
  exact
    { r0 := h0
      r1 := h1
      r12 := h12
      sp16 := by rw [k.sp]; have := hp.sp24; omega
      cw := by
        rw [ea, eh]
        exact Covers.of_sub fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · exact cov_part hp k (by omega)
          · exact cov_part hp k (by omega)
          · exact cov_low hp k (by omega)
      st_o := by rw [ea, eh]; exact part_disj hz (Or.inl (by omega)) (by omega) (by omega)
      st_sc := by rw [ea]; exact (low_disj hz (k := hH.Wb) (by omega) (by omega)).symm
      o_sc := by rw [eh]; exact (low_disj hz (k := hH.Wb) (by omega) (by omega)).symm
      b_st := by rw [ea]; exact b16 hp k (part_sub (by omega))
      b_o := by rw [eh]; exact b16 hp k (part_sub (by omega))
      b_sc := b16 hp k (low_sub (by omega))
      nst := by rw [dO_toNat hp (by omega)]; have := hp.nsc; omega
      no := by rw [dO_toNat hp (by omega)]; have := hp.nsc; omega
      nsc := by have := hp.nsc; omega }

theorem hk6_ok {s : State} (hk : KK F s₀ s) (h0 : s.gpr .r0 = dO s₀ F.stWO) (h1 : s.gpr .r1 = dO s₀ F.hkO)
    (h12 : s.gpr .r12 = scr s₀) (hc : count s = BitVec.ofNat 64 (pwl s₀))
    (hr : hH.SH.Repr s.mem (A s₀ F.stWO) (bytesAt s₀.mem (State.addr (pw s₀)) (pwl s₀))) :
    WP isa (.frame (.push [.r1, .r12]) (.call F.H.finN F.H.finC) (.pop .r1 8)) s
      fun t => KR F s₀ t ∧
        bytesAt t.mem (A s₀ F.hkO) F.H.D = hH.SH.H.hash (bytesAt s₀.mem (State.addr (pw s₀)) (pwl s₀)) := by
  have hl := layout (F := F); have he := end_le hz; have := hz.S; have := hz.D; have := hz.W; have := hz.reach
  have := hH.hWb
  have ea := dO_addr hp (o := F.stWO) (by omega)
  have eh := dO_addr hp (o := F.hkO) (by omega)
  refine fin_frame hH (hk6_args hp hz hH hk h0 h1 h12) fun s' a r => ⟨hk.kr.call hp hz (After.of_hmac a)
    fun r hr => ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inr ⟨_, _, by rw [ea], by omega, by omega⟩
    · exact .inr ⟨_, _, by rw [eh], by omega, by omega⟩
    · exact .inl ⟨_, rfl, by omega⟩
  · rw [bytesAt_take _ _ hz.D.2.1, ← eh]
    exact r _ (by rw [ea]; exact hr) (by rw [bytesAt_length]; exact Nat.lt_trans (s₀.gpr .r1).isLt (by decide))
      (by rw [bytesAt_length]; exact hc)

omit hp hz hH in
theorem hk7_ok {s : State} (hk : KR F s₀ s) (ho : F.hkO < 2 ^ 16) (hD : F.H.D < 2 ^ 16) :
    WP isa (.block (scrAt .r2 F.hkO ++ [.movw .r3 (BitVec.ofNat 16 F.H.D)])) s
      fun t => KR F s₀ t ∧ t.gpr .r2 = dO s₀ F.hkO ∧ t.gpr .r3 = BitVec.ofNat 32 F.H.D ∧ t.mem = s.mem :=
  scr_ok hk ho fun s₁ u₁ => Hmac.Generic.Arm.wp_movw fun s₂ u₂ => WP.block_nil
    ⟨(hk.upd12 (by decide) u₁).upd (by decide) u₂, by rw [u₂.other _ (by decide), u₁.gpr],
      by rw [u₂.gpr, Hmac.Generic.Arm.movw_ofNat hD], by rw [u₂.mem, u₁.mem]⟩

theorem hashKey_ok {s : State} (hk : KK F s₀ s) :
    WP isa F.hashKey s fun t => KR F s₀ t ∧ t.gpr .r2 = dO s₀ F.hkO ∧ t.gpr .r3 = BitVec.ofNat 32 F.H.D ∧
      bytesAt t.mem (A s₀ F.hkO) F.H.D = hH.SH.H.hash (bytesAt s₀.mem (State.addr (pw s₀)) (pwl s₀)) := by
  have hl := layout (F := F); have he := end_le hz; have := hz.S; have := hz.D; have := hz.reach
  unfold Fns.hashKey
  refine WP.seq (WP.mono (hk1_ok hk (by omega)) fun s₁ ⟨k₁, d₁, _⟩ => ?_)
  refine WP.seq (WP.mono (hk2_ok hp hz hH k₁ d₁) fun s₂ ⟨k₂, r₂, e₂⟩ => ?_)
  refine WP.seq (WP.mono (hk3_ok k₂ e₂) fun s₃ ⟨k₃, d₃, a₀, a₁, a₇, a₁₀, c₃, m₃⟩ => ?_)
  refine WP.seq (WP.mono (hk4_ok hp hz hH k₃ d₃ a₀ a₁ a₇ a₁₀ c₃ (by rw [m₃]; exact r₂)) fun s₄ ⟨k₄, d₄, r₄⟩ => ?_)
  refine WP.seq (WP.mono (hk5_ok k₄ d₄ (by omega)) fun s₅ ⟨k₅, a₀', a₁', a₁₂, c₅, m₅⟩ => ?_)
  refine WP.seq (WP.mono (hk6_ok hp hz hH k₅ a₀' a₁' a₁₂ c₅ (by rw [m₅]; exact r₄)) fun s₆ ⟨k₆, b₆⟩ => ?_)
  exact WP.mono (hk7_ok k₆ (by omega) (by omega)) fun t ⟨k, d, c, m⟩ => ⟨k, d, c, by rw [m]; exact b₆⟩

end

/-! ## The key -/

section
variable {s₀ : State} (hp : Pre F s₀) (hz : Sizes F) (hH : HashOK F.H)
include hp hz

omit hp in
theorem cmp_ok {s : State} (hk : KK F s₀ s) :
    WP isa (.block F.cmpPw) s fun t => KK F s₀ t ∧ t.z = decide (pwl s₀ < F.H.B + 1) ∧ t.mem = s.mem := by
  have := hz.B
  unfold Fns.cmpPw
  rw [← List.append_nil [Instr.subs .r12 .r9 (.imm (BitVec.ofNat 32 (F.H.B + 1))), .mov .r12 (.imm 0),
    .adc .r12 .r12 (.imm 0), .cmp .r12 (.imm 0)]]
  refine wp_lt hz.encB1 fun s' g m rd wr sp z => WP.block_nil ⟨⟨hk.kr.same rd wr sp (fun r hr => g r (by
    simp only [kregs, List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide)) m,
    by rw [g _ (by decide), hk.r8], by rw [g _ (by decide), hk.r9]⟩, ?_, m⟩
  rw [z, hk.r9, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := F.H.B + 1) (by omega)]

omit hp hz in
include hH in
theorem hash_len {k : List Byte} {m : Mem} {p : Addr} (h : bytesAt m p F.H.D = hH.SH.H.hash k) :
    (hH.SH.H.hash k).length = F.H.D := by
  rw [← h, bytesAt_length]

omit hp in
include hH in
/-- A key longer than a block and its digest give the same `K₀`. -/
theorem blockKey_hash {k : List Byte} (hk : F.H.B < k.length) (hl : (hH.SH.H.hash k).length = F.H.D) :
    blockKey hH.SH.H (hH.SH.H.hash k) = blockKey hH.SH.H k := by
  have hB := hH.hB; have := hz.DB
  simp only [blockKey, hB, hl, ite_eq_left_of_eq_true _ _ (eq_true hk),
    ite_eq_right_of_eq_false _ _ (eq_false (show ¬ F.H.B < F.H.D by omega))]

end

/-- Where the key is, and its length. -/
abbrev kp (F : Fns) (s₀ : State) : BitVec 32 := if pwl s₀ < F.H.B + 1 then pw s₀ else dO s₀ F.hkO
abbrev kl (F : Fns) (s₀ : State) : Nat := if pwl s₀ < F.H.B + 1 then pwl s₀ else F.H.D

section
variable {s₀ : State} (hp : Pre F s₀) (hz : Sizes F) (hH : HashOK F.H)
include hp hz hH

theorem key_ok {s : State} (hk : KK F s₀ s) :
    WP isa F.key s fun t => KR F s₀ t ∧ t.gpr .r2 = kp F s₀ ∧ t.gpr .r3 = BitVec.ofNat 32 (kl F s₀) ∧
      blockKey hH.SH.H (bytesAt t.mem (State.addr (kp F s₀)) (kl F s₀)) =
        blockKey hH.SH.H (bytesAt s₀.mem (State.addr (pw s₀)) (pwl s₀)) := by
  unfold Fns.key
  refine WP.seq (WP.mono (cmp_ok hz hk) fun s₁ ⟨k₁, z₁, _⟩ => ?_)
  refine WP.ite (decide (pwl s₀ < F.H.B + 1)) (by show eval .eq s₁ = _; rw [eval_eq, z₁]) (fun hT => ?_) fun hF => ?_
  · have hlt : pwl s₀ < F.H.B + 1 := of_decide_eq_true hT
    simp only [kp, kl, hlt, ↓reduceIte]
    refine wp_mov (op2_reg _ _) fun s₂ u₂ => wp_mov (op2_reg _ _) fun s₃ u₃ => WP.block_nil
      ⟨(k₁.kr.upd (by decide) u₂).upd (by decide) u₃, ?_, ?_, ?_⟩
    · rw [u₃.other _ (by decide), u₂.gpr, k₁.r8]
    · rw [u₃.gpr, u₂.other _ (by decide), k₁.r9, ofNat_toNat32]
    · rw [u₃.mem, u₂.mem, k₁.kr.pwBytes hp]
  · have hlt : ¬ pwl s₀ < F.H.B + 1 := of_decide_eq_false hF
    simp only [kp, kl, hlt, ↓reduceIte]
    refine WP.mono (hashKey_ok hp hz hH k₁) fun t ⟨k, d, c, b⟩ => ⟨k, d, c, ?_⟩
    have := hz.D; have := hz.reach
    rw [dO_addr hp (by have := end_le hz; have := layout (F := F); omega),
      b, blockKey_hash hz hH (by rw [bytesAt_length]; omega) (hash_len hH b)]

omit hH in
/-- The key's region is the password, or the hashed password in `scratch`. -/
theorem key_cases : (kp F s₀ = pw s₀ ∧ kl F s₀ = pwl s₀ ∧ pwl s₀ ≤ F.H.B) ∨
    (State.addr (kp F s₀) = A s₀ F.hkO ∧ kl F s₀ = F.H.D) := by
  by_cases h : pwl s₀ < F.H.B + 1
  · exact .inl ⟨by simp [kp, h], by simp [kl, h], by omega⟩
  · refine .inr ⟨?_, by simp [kl, h]⟩
    simp only [kp, h, ↓reduceIte]
    exact dO_addr hp (by have := end_le hz; have := layout (F := F); have := hz.D; omega)

omit hH in
theorem kl_le : kl F s₀ ≤ F.H.B := by
  have := hz.DB
  rcases key_cases hp hz with ⟨-, h, h'⟩ | ⟨-, h⟩ <;> omega

omit hH in
theorem key_toNat : (kp F s₀).toNat + kl F s₀ ≤ 2 ^ 32 := by
  by_cases h : pwl s₀ < F.H.B + 1
  · simp only [kp, kl, h, ↓reduceIte]; exact hp.npw
  · simp only [kp, kl, h, ↓reduceIte]
    have := end_le hz; have := layout (F := F); have := hz.D
    rw [dO_toNat hp (by omega)]
    have := hp.nsc; omega

omit hH in
/-- The key is apart from the parts of `scratch` after the hashed password,
from the working space, and from the stack below the stack pointer. -/
theorem key_disj {R : Region} (hR : Region.Sub R (scR s₀ F))
    (hd : R.Disjoint (sR s₀ F.hkO F.H.D)) : Region.Disjoint ⟨State.addr (kp F s₀), kl F s₀⟩ R := by
  rcases key_cases hp hz with ⟨h, h', -⟩ | ⟨h, h'⟩
  · rw [h, h']; exact hp.pw_s.sub_right hR
  · rw [h, h']; exact hd.symm

omit hH in
theorem key_stk {s : State} (hk : KR F s₀ s) : (stk s).Disjoint ⟨State.addr (kp F s₀), kl F s₀⟩ := by
  rw [hk.stkE]
  rcases key_cases hp hz with ⟨h, h', -⟩ | ⟨h, h'⟩
  · rw [h, h']; exact hp.b_pw
  · rw [h, h']; exact hp.b_s.sub_right (part_sub (by have := end_le hz; have := layout (F := F); have := hz.D; omega))

omit hH in
theorem key_cov {s : State} (hk : KR F s₀ s) : Covers [⟨State.addr (kp F s₀), kl F s₀⟩] (s.rd ++ s.wr) := by
  rcases key_cases hp hz with ⟨h, h', -⟩ | ⟨h, h'⟩
  · rw [h, h']; exact cov_pw hp hk
  · rw [h, h']
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      obtain ⟨r', hr', off, e, l⟩ := cov_part hp hk (o := F.hkO) (n := F.H.D)
        (by have := end_le hz; have := layout (F := F); have := hz.D; omega)
      exact ⟨r', List.mem_append_right _ hr', off, e, l⟩

end

end VG.Proof.Pbkdf2.Whole.Arm
