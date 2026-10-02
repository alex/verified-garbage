import VerifiedGarbage.Proof.AesGcm.Arm.CTVerify
import VerifiedGarbage.Proof.AesGcm.Arm.Open

/-!
# AES-GCM on ARMv7: the pieces of `seal` and `open` are constant time

Untrusted: everything here is checked by Lean. Each piece is related across
two runs from `s₀` and `s₀'` with the same public data (`onePub`), from
what it needs in each run, to what the next piece needs.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcm.Arm
open VG.Spec.Gcm (Block blockAt)

/-- A relation of two runs of `c` carries what a further `R` reaches from them. -/
theorem rel_ghost {F F' G G' Z Z' : State → Prop} {c R : Prog isa}
    (h : RelCT isa (fun a b => F a ∧ F' b) c fun a b => G a ∧ G' b) :
    RelCT isa (fun a b => (F a ∧ WP isa (.seq c R) a Z) ∧ (F' b ∧ WP isa (.seq c R) b Z')) c
      fun a b => (G a ∧ WP isa R a Z) ∧ (G' b ∧ WP isa R b Z') := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨ht, hg, hg'⟩ := h _ _ _ _ _ _ ⟨hp.1.1, hp.2.1⟩ e₁ e₂
  obtain ⟨u₁, x₁, f₁, w₁⟩ := WP.seq_iff.mp hp.1.2
  obtain ⟨u₂, x₂, f₂, w₂⟩ := WP.seq_iff.mp hp.2.2
  obtain ⟨-, rfl⟩ := Exec.det f₁ e₁
  obtain ⟨-, rfl⟩ := Exec.det f₂ e₂
  exact ⟨ht, ⟨hg, w₁⟩, ⟨hg', w₂⟩⟩

theorem wp_nil {s : State} {Q : State → Prop} (h : WP isa (.block []) s Q) : Q s := by
  obtain ⟨t, s', e, hq⟩ := h
  rw [Exec.block_iff] at e
  simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at e
  obtain ⟨rfl, -⟩ := e
  exact hq

/-- The stack arguments are apart from what the code writes. -/
theorem one_hw {n : Nat} {t : State} (ht : onePre n t) : ∀ r ∈ t.wr, (args t n).Disjoint r := by
  intro r hr
  rw [ht.2.1] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ht.2.2.2.2.2.2.2.2.2.1.symm
  · exact ht.2.2.2.2.2.2.2.2.2.2.1.symm

/-- A block reading stack arguments below 20 is constant time in two runs that keep them. -/
theorem argsR {na : Nat} (hna : 5 ≤ na) {t₀ t₀' : State} (hsp : t₀.sp = t₀'.sp)
    (hf : t₀.sp.toNat + 4 * na ≤ 2 ^ 32) (ha : ∀ i < na, arg t₀ i = arg t₀' i)
    (hw : ∀ r ∈ t₀.wr, (args t₀ na).Disjoint r) (hw' : ∀ r ∈ t₀'.wr, (args t₀' na).Disjoint r)
    {b : List Instr} (hb : ∃ hc, (taint.check (argTaint [] (4 * 5)) (.block b) hc).isSome = true)
    {P P' : State → Prop} (hP : ∀ s, P s → ArgsKeep na t₀ s) (hP' : ∀ s, P' s → ArgsKeep na t₀' s) :
    RelCT isa (fun a b => P a ∧ P' b) (.block b) fun _ _ => True := by
  obtain ⟨_, hc⟩ := hb
  exact RelCT.taint (A := taint) (argTaint [] (4 * 5)) (fun s s' h =>
    ((hP _ h.1).weaken hna).agree ((hP' _ h.2).weaken hna) hsp (by omega) (fun i hi => ha i (by omega))
      (fun r hr => (hw r hr).sub_left (args_sub _ hna)) (fun r hr => (hw' r hr).sub_left (args_sub _ hna))
      (by simp)) hc

/-! ## Each run -/

section
variable {na : Nat} {t₀ : State} {c w sp : BitVec 32} {R : Nat}

theorem so1_FT {s : State} (h1 : SO1 na t₀ s) (ec : t₀.gpr .r0 = c) (ew : arg t₀ 4 = w) (esp : t₀.sp = sp)
    (eR : (t₀.gpr .r1).toNat = R) : FT na t₀ c (w + BitVec.ofNat 32 16) w sp R s := by
  subst ec ew esp eR
  exact ⟨_, by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; exact h1.env, h1.args⟩

theorem j0_wpI (h : onePre na t₀) (ec : t₀.gpr .r0 = c) (ew : arg t₀ 4 = w) (esp : t₀.sp = sp) {s : State}
    (hs : FT na t₀ c (w + BitVec.ofNat 32 16) w sp R s) (h4 : s.gpr .r4 = t₀.gpr .r2)
    (h5 : s.gpr .r5 = t₀.gpr .r3) :
    J0I c (w + BitVec.ofNat 32 16) w sp (t₀.gpr .r2) (t₀.gpr .r3).toNat s ∧
      WP isa j0 s (FT na t₀ c (w + BitVec.ofNat 32 16) w sp R) := by
  subst ec ew esp
  have L := oneLay h
  have spf := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨k7, he, hk⟩ := hs
  have hp := h
  obtain ⟨hrd, -, -, -, -, dnW, -, -, -, -, -, -, bn, -, -, -, -, fn, -⟩ := hp
  have ji : J0In (t₀.gpr .r0) (oSt t₀) (arg t₀ 4) t₀.sp k7 (BitVec.ofNat 32 R)
      (blockAt s.mem (State.addr (t₀.gpr .r0) + BitVec.ofNat 64 240)) (t₀.gpr .r2) (t₀.gpr .r3).toNat s :=
    ⟨he, rfl, h4, by rw [h5]; simp, ⟨by rw [hk.rd, hk.wr, hrd]; exact covers_of_mem (by simp),
      (t₀.gpr .r3).isLt, fn, oSt_disj h dnW, dnW, bn⟩⟩
  exact ⟨⟨_, _, _, ji⟩, WP.mono (WP.with_rdwr (j0_ok L ji)) fun s' ⟨jo, rd', wr', sp'⟩ =>
    ⟨jo.env.choose, jo.env.choose_spec, hk.frame spf jo.frame (one_argsJ0 h) sp' rd' wr'⟩⟩

variable {st : BitVec 32}

theorem b1_wpI (hf : t₀.sp.toNat + 4 * na ≤ 2 ^ 32) (hin : args t₀ na ∈ t₀.rd) (hn : 5 ≤ na) {s : State}
    (hs : FT na t₀ c st w sp R s) :
    WP isa (.block [.ldrSp .r4 0, .ldrSp .r5 4, .mov .r6 (imm 0)]) s fun s' => FT na t₀ c st w sp R s' ∧
      s'.gpr .r4 = arg t₀ 0 ∧ s'.gpr .r5 = arg t₀ 1 ∧ s'.gpr .r6 = BitVec.ofNat 32 0 := by
  obtain ⟨k7, he, hk⟩ := hs
  obtain ⟨a0, v0⟩ := hk.at hf hin 0 (by omega) (show 4 * 0 = 0 from rfl)
  obtain ⟨a1, v1⟩ := hk.at hf hin 1 (by omega) (show 4 * 1 = 4 from rfl)
  refine WP.of_runBlock ⟨_, by arun [a0, v0, a1, v1], ?_⟩
  refine ⟨⟨k7, he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg]) rfl rfl rfl, hk.of_eq rfl rfl rfl rfl⟩,
    ?_, ?_, ?_⟩
  · simp [gpr_setReg, v0]
  · simp [gpr_setReg, v1]
  · simp [gpr_setReg]

theorem b2_wpI (hf : t₀.sp.toNat + 4 * na ≤ 2 ^ 32) (hin : args t₀ na ∈ t₀.rd) (hn : 5 ≤ na) {s : State}
    (hs : FT na t₀ c st w sp R s) :
    WP isa (.block [.ldrSp .r6 4, .dp .and .r6 .r6 (imm 15)]) s fun s' => FT na t₀ c st w sp R s' ∧
      s'.gpr .r6 = BitVec.ofNat 32 ((arg t₀ 1).toNat % 16) := by
  obtain ⟨k7, he, hk⟩ := hs
  obtain ⟨b1, w1⟩ := hk.at hf hin 1 (by omega) (show 4 * 1 = 4 from rfl)
  refine WP.of_runBlock ⟨_, by arun [b1, w1], ?_⟩
  refine ⟨⟨k7, he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg]) rfl rfl rfl, hk.of_eq rfl rfl rfl rfl⟩, ?_⟩
  simp only [gpr_setReg, ite_true, w1, and15]

theorem b3_wpI (hf : t₀.sp.toNat + 4 * na ≤ 2 ^ 32) (hin : args t₀ na ∈ t₀.rd) (hn : 5 ≤ na) {s : State}
    (hs : FT na t₀ c st w sp R s) :
    WP isa (.block [.ldrSp .r6 12, .dp .and .r6 .r6 (imm 15)]) s fun s' => FT na t₀ c st w sp R s' ∧
      s'.gpr .r6 = BitVec.ofNat 32 ((arg t₀ 3).toNat % 16) := by
  obtain ⟨k7, he, hk⟩ := hs
  obtain ⟨b3, w3⟩ := hk.at hf hin 3 (by omega) (show 4 * 3 = 12 from rfl)
  refine WP.of_runBlock ⟨_, by arun [b3, w3], ?_⟩
  refine ⟨⟨k7, he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg]) rfl rfl rfl, hk.of_eq rfl rfl rfl rfl⟩, ?_⟩
  simp only [gpr_setReg, ite_true, w3, and15]

theorem b4_wpI (hf : t₀.sp.toNat + 4 * na ≤ 2 ^ 32) (hin : args t₀ na ∈ t₀.rd) (hn : 5 ≤ na) {s : State}
    (hs : FT na t₀ c st w sp R s) :
    WP isa (.block [.ldrSp .r4 4, .mov .r5 (imm 0), .ldrSp .r6 12, .mov .r7 (imm 0)]) s
      (FT na t₀ c st w sp R) := by
  obtain ⟨k7, he, hk⟩ := hs
  obtain ⟨j1, w1⟩ := hk.at hf hin 1 (by omega) (show 4 * 1 = 4 from rfl)
  obtain ⟨j3, w3⟩ := hk.at hf hin 3 (by omega) (show 4 * 3 = 12 from rfl)
  refine WP.of_runBlock ⟨_, by arun [j1, w1, j3, w3], ?_⟩
  exact ⟨_, he.set7 (k7' := BitVec.ofNat 32 0) (by simp [gpr_setReg]) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> simp [gpr_setReg]) rfl rfl rfl, hk.of_eq rfl rfl rfl rfl⟩

theorem da_wpI (hf : t₀.sp.toNat + 4 * na ≤ 2 ^ 32) (hin : args t₀ na ∈ t₀.rd) (hn : 5 ≤ na) {s : State}
    (hs : FT na t₀ c st w sp R s) :
    WP isa (.block dataArgs) s fun s' => FT na t₀ c st w sp R s' ∧
      s'.gpr .r4 = arg t₀ 2 ∧ s'.gpr .r5 = arg t₀ 3 ∧ s'.gpr .r6 = BitVec.ofNat 32 0 := by
  obtain ⟨k7, he, hk⟩ := hs
  obtain ⟨s', run, h4, h5, h6, g, k⟩ := dataArgs_run hk hf hin hn
  exact WP.of_runBlock ⟨s', run, ⟨k7, he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact g _ (by decide) (by decide) (by decide)) k.sp k.rd k.wr,
    hk.of_eq k.mem k.sp k.rd k.wr⟩, h4, h5, h6⟩

variable (L : Lay c st w sp)
include L

theorem abs_wpI (hf : t₀.sp.toNat + 4 * na ≤ 2 ^ 32) (hJ : ∀ r ∈ j0Frame st w sp, (args t₀ na).Disjoint r)
    {D : BitVec 32} {n : Nat} (hd : DataOk st w sp t₀ D n) {s : State} (hs : FT na t₀ c st w sp R s)
    (h4 : s.gpr .r4 = D) (h5 : s.gpr .r5 = BitVec.ofNat 32 n) (h6 : s.gpr .r6 = BitVec.ofNat 32 0) :
    AbsI c st w sp 16 D n 0 s ∧ WP isa (absorb 16) s (FT na t₀ c st w sp R) := by
  obtain ⟨k7, he, hk⟩ := hs
  have ai : AbsIn c st w sp k7 (BitVec.ofNat 32 R) 16 (blockAt s.mem (State.addr c + BitVec.ofNat 64 240)) []
      D n s := ⟨he, h4, h5, by rw [h6]; rfl, hd.of_eq hk.rd hk.wr, rfl⟩
  exact ⟨⟨_, _, _, _, rfl, ai⟩, WP.mono (WP.with_rdwr (absorb_ok L (.inr rfl) ai)) fun s' ⟨ab, rd', wr', sp'⟩ =>
    ⟨k7, ab.env, hk.frame hf ab.frame (disj_sub hJ abs16_sub) sp' rd' wr'⟩⟩

theorem fl_wpI (hf : t₀.sp.toNat + 4 * na ≤ 2 ^ 32) (hJ : ∀ r ∈ j0Frame st w sp, (args t₀ na).Disjoint r)
    {q : Nat} (hq : q < 16) {s : State} (hs : FT na t₀ c st w sp R s) (h6 : s.gpr .r6 = BitVec.ofNat 32 q) :
    WP isa (flush 16) s (FT na t₀ c st w sp R) := by
  obtain ⟨k7, he, hk⟩ := hs
  exact WP.mono (WP.with_rdwr (flush_ok L (yo := 16) (.inr rfl) (x := List.replicate q 0)
    (H := blockAt s.mem (State.addr c + BitVec.ofNat 64 240)) ⟨he, rfl⟩ (by simp [h6, Nat.mod_eq_of_lt hq])))
    fun s' ⟨fl, rd', wr', sp'⟩ => ⟨k7, fl.env, hk.frame hf fl.frame (disj_sub hJ t16_sub) sp' rd' wr'⟩

theorem cr_wpI (hf : t₀.sp.toNat + 4 * na ≤ 2 ^ 32) {D : BitVec 32} {n : Nat} (hd : DataOk st w sp t₀ D n)
    (hwD : Covers [⟨State.addr D, n⟩] t₀.wr) (hcD : (⟨State.addr c, 256⟩ : Region).Disjoint ⟨State.addr D, n⟩)
    (hA : ∀ r ∈ crFrame st w sp D n, (args t₀ na).Disjoint r) (hR : R = 10 ∨ R = 12 ∨ R = 14) {s : State}
    (hs : FT na t₀ c st w sp R s) (h4 : s.gpr .r4 = D) (h5 : s.gpr .r5 = BitVec.ofNat 32 n)
    (h6 : s.gpr .r6 = BitVec.ofNat 32 0) :
    CrI c st w sp (BitVec.ofNat 32 R) R D n 0 s ∧ WP isa crypt s (FT na t₀ c st w sp R) := by
  obtain ⟨k7, he, hk⟩ := hs
  have ci : CrIn c st w sp k7 (BitVec.ofNat 32 R) R (blockAt s.mem (State.addr st + BitVec.ofNat 64 48)) 0 D n s :=
    ⟨he, h4, h5, by rw [h6], he.r8, hR, ⟨hd.of_eq hk.rd hk.wr, by rw [hk.wr]; exact hwD, hcD⟩⟩
  exact ⟨⟨_, _, _, rfl, ci⟩, WP.mono (WP.with_rdwr (crypt_ok L ci)) fun s' ⟨co, rd', wr', sp'⟩ =>
    ⟨k7, co.env, hk.frame hf co.frame hA sp' rd' wr'⟩⟩

theorem tg_wpI (hf : t₀.sp.toNat + 4 * na ≤ 2 ^ 32) {o : Nat} (ho : o = 0 ∨ o = 112)
    (hT : ∀ r ∈ tagFrame st w sp o, (args t₀ na).Disjoint r) (hR : R = 10 ∨ R = 12 ∨ R = 14) {s : State}
    (hs : FT na t₀ c st w sp R s) : WP isa (tag o) s (FT na t₀ c st w sp R) := by
  obtain ⟨k7, he, hk⟩ := hs
  exact WP.mono (WP.with_rdwr (tag_ok L ho he rfl hR rfl rfl)) fun s' ⟨tg, rd', wr', sp'⟩ =>
    ⟨k7, tg.env, hk.frame hf tg.frame hT sp' rd' wr'⟩

end

end VG.Proof.AesGcm.Arm
