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

/-! ## Both runs -/

theorem one_aadOk {n : Nat} {t : State} (h : onePre n t) :
    DataOk (oSt t) (arg t 4) t.sp t (arg t 0) (arg t 1).toNat := by
  have hp := h
  obtain ⟨hrd, -, -, -, -, -, -, daW, -, -, -, -, -, ba, -, -, -, -, fa, -⟩ := hp
  exact ⟨by rw [hrd]; exact covers_of_mem (by simp), (arg t 1).isLt, fa, oSt_disj h daW, daW, ba⟩

theorem one_argsCr {n : Nat} {t : State} (h : onePre n t) :
    ∀ r ∈ crFrame (oSt t) (arg t 4) t.sp (arg t 2) (arg t 3).toNat, (args t n).Disjoint r := by
  have hst := oSt_addr h
  have spf := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨-, -, -, -, -, -, -, -, -, dDA, dWA, -⟩ := h
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact dDA.symm
  · rw [hst, add_ofNat_assoc]; exact (dWA.sub_left (Lay.wSub (by decide))).symm
  · exact (dWA.sub_left (Lay.wSub (by decide))).symm
  · exact (below_args t spf).symm

/-- A run's state, with the public data of `s₀` and the stack arguments of `t₀`. -/
abbrev OF (na : Nat) (s₀ t₀ s : State) : Prop :=
  FT na t₀ (s₀.gpr .r0) (oSt s₀) (arg s₀ 4) s₀.sp (s₀.gpr .r1).toNat s

section
variable {na : Nat} {s₀ s₀' : State} (h0 : onePre na s₀) (h0' : onePre na s₀') (hq : onePub na s₀ s₀')
  (hn : 5 ≤ na)
include h0 h0' hq hn

theorem oneAad_rel :
    RelCT isa (fun a b => SO1 na s₀ a ∧ SO1 na s₀' b) oneAad fun a b => OF na s₀ s₀ a ∧ OF na s₀ s₀' b := by
  obtain ⟨q₀, q₁, q₂, q₃, q₄, qa⟩ := hq
  have L := oneLay h0
  have spf := h0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have spf' := h0'.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hin : args s₀ na ∈ s₀.rd := by rw [h0.1]; simp
  have hin' : args s₀' na ∈ s₀'.rd := by rw [h0'.1]; simp
  have e4 : arg s₀' 4 = arg s₀ 4 := (qa 4 (by omega)).symm
  have est : oSt s₀' = oSt s₀ := by show arg s₀' 4 + _ = arg s₀ 4 + _; rw [e4]
  have hJ := one_argsJ0 h0
  have hJ' : ∀ r ∈ j0Frame (oSt s₀) (arg s₀ 4) s₀.sp, (args s₀' na).Disjoint r := by
    have := one_argsJ0 h0'; rwa [est, e4, ← q₀] at this
  have so : ∀ s, SO1 na s₀ s → OF na s₀ s₀ s := fun s h1 => so1_FT h1 rfl rfl rfl rfl
  have so' : ∀ s, SO1 na s₀' s → OF na s₀ s₀' s := fun s h1 => so1_FT h1 q₁.symm e4 q₀.symm (by rw [q₂])
  -- `J₀`
  have x1 := rel_wp (F := SO1 na s₀) (F' := SO1 na s₀') (G := OF na s₀ s₀) (G' := OF na s₀ s₀')
    (rel_of_ct (j0_ct L (Np := s₀.gpr .r2) (n := (s₀.gpr .r3).toNat) (s₀.gpr .r3).isLt)
      (fun s h1 => (j0_wpI h0 rfl rfl rfl (so s h1) h1.r4 h1.r5).1)
      (fun s h1 => by
        have := (j0_wpI h0' q₁.symm e4 q₀.symm (so' s h1) h1.r4 h1.r5).1
        rwa [← q₃, ← q₄] at this))
    (fun s h1 => (j0_wpI h0 rfl rfl rfl (so s h1) h1.r4 h1.r5).2)
    (fun s h1 => (j0_wpI h0' q₁.symm e4 q₀.symm (so' s h1) h1.r4 h1.r5).2)
  -- the additional data's arguments
  let B1 : State → State → Prop := fun t₀ s => OF na s₀ t₀ s ∧ s.gpr .r4 = arg s₀ 0 ∧
    s.gpr .r5 = arg s₀ 1 ∧ s.gpr .r6 = BitVec.ofNat 32 0
  have x2 := rel_wp (F := OF na s₀ s₀) (F' := OF na s₀ s₀') (G := B1 s₀) (G' := B1 s₀')
    (argsR hn q₀ spf qa (one_hw h0) (one_hw h0') ⟨_, by taint_decide⟩ (fun s h => h.choose_spec.2)
      (fun s h => h.choose_spec.2))
    (fun s h => b1_wpI spf hin hn h)
    (fun s h => WP.mono (b1_wpI spf' hin' hn h) fun s' ⟨y₁, y₂, y₃, y₄⟩ =>
      ⟨y₁, by rw [y₂, qa 0 (by omega)], by rw [y₃, qa 1 (by omega)], y₄⟩)
  -- absorbed
  have hda := one_aadOk h0
  have hda' : DataOk (oSt s₀) (arg s₀ 4) s₀.sp s₀' (arg s₀ 0) (arg s₀ 1).toNat := by
    have := one_aadOk h0'; rwa [est, e4, ← q₀, ← qa 0 (by omega), ← qa 1 (by omega)] at this
  have x3 := rel_wp (F := B1 s₀) (F' := B1 s₀') (G := OF na s₀ s₀) (G' := OF na s₀ s₀')
    (rel_of_ct (absorb_ct L (yo := 16) (.inr rfl) (D := arg s₀ 0) (n := (arg s₀ 1).toNat) (q := 0) (by decide))
      (fun s h => (abs_wpI L spf hJ hda h.1 h.2.1 (by rw [h.2.2.1]; simp) h.2.2.2).1)
      (fun s h => (abs_wpI L spf' hJ' hda' h.1 h.2.1 (by rw [h.2.2.1]; simp) h.2.2.2).1))
    (fun s h => (abs_wpI L spf hJ hda h.1 h.2.1 (by rw [h.2.2.1]; simp) h.2.2.2).2)
    (fun s h => (abs_wpI L spf' hJ' hda' h.1 h.2.1 (by rw [h.2.2.1]; simp) h.2.2.2).2)
  -- padded
  let B2 : State → State → Prop := fun t₀ s => OF na s₀ t₀ s ∧
    s.gpr .r6 = BitVec.ofNat 32 ((arg s₀ 1).toNat % 16)
  have x4 := rel_wp (F := OF na s₀ s₀) (F' := OF na s₀ s₀') (G := B2 s₀) (G' := B2 s₀')
    (argsR hn q₀ spf qa (one_hw h0) (one_hw h0') ⟨_, by taint_decide⟩ (fun s h => h.choose_spec.2)
      (fun s h => h.choose_spec.2))
    (fun s h => b2_wpI spf hin hn h)
    (fun s h => WP.mono (b2_wpI spf' hin' hn h) fun s' ⟨y₁, y₂⟩ => ⟨y₁, by rw [y₂, qa 1 (by omega)]⟩)
  have x5 := rel_wp (F := B2 s₀) (F' := B2 s₀') (G := OF na s₀ s₀) (G' := OF na s₀ s₀')
    (rel_of_ct (flush_ct L (yo := 16) (.inr rfl) (q := (arg s₀ 1).toNat % 16) (Nat.mod_lt _ (by decide)))
      (fun s ⟨⟨k7, he, _⟩, h6⟩ => ⟨k7, _, he, h6⟩) (fun s ⟨⟨k7, he, _⟩, h6⟩ => ⟨k7, _, he, h6⟩))
    (fun s h => fl_wpI L spf hJ (Nat.mod_lt _ (by decide)) h.1 h.2)
    (fun s h => fl_wpI L spf' hJ' (Nat.mod_lt _ (by decide)) h.1 h.2)
  exact x1.seq (x2.seq (x3.seq (x4.seq x5)))

theorem oneCrypt_rel :
    RelCT isa (fun a b => OF na s₀ s₀ a ∧ OF na s₀ s₀' b) oneCrypt fun a b => OF na s₀ s₀ a ∧ OF na s₀ s₀' b := by
  obtain ⟨q₀, q₁, q₂, q₃, q₄, qa⟩ := hq
  have L := oneLay h0
  have spf := h0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have spf' := h0'.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hR : roundsOk s₀ := h0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hin : args s₀ na ∈ s₀.rd := by rw [h0.1]; simp
  have hin' : args s₀' na ∈ s₀'.rd := by rw [h0'.1]; simp
  have e4 : arg s₀' 4 = arg s₀ 4 := (qa 4 (by omega)).symm
  have est : oSt s₀' = oSt s₀ := by show arg s₀' 4 + _ = arg s₀ 4 + _; rw [e4]
  let D1 : State → State → Prop := fun t₀ s => OF na s₀ t₀ s ∧ s.gpr .r4 = arg s₀ 2 ∧
    s.gpr .r5 = arg s₀ 3 ∧ s.gpr .r6 = BitVec.ofNat 32 0
  have x1 := rel_wp (F := OF na s₀ s₀) (F' := OF na s₀ s₀') (G := D1 s₀) (G' := D1 s₀')
    (argsR hn q₀ spf qa (one_hw h0) (one_hw h0') ⟨_, by taint_decide⟩ (fun s h => h.choose_spec.2)
      (fun s h => h.choose_spec.2))
    (fun s h => da_wpI spf hin hn h)
    (fun s h => WP.mono (da_wpI spf' hin' hn h) fun s' ⟨y₁, y₂, y₃, y₄⟩ =>
      ⟨y₁, by rw [y₂, qa 2 (by omega)], by rw [y₃, qa 3 (by omega)], y₄⟩)
  have hd := one_dataOk h0 (ArgsKeep.refl na s₀)
  have hd' : DataOk (oSt s₀) (arg s₀ 4) s₀.sp s₀' (arg s₀ 2) (arg s₀ 3).toNat := by
    have := one_dataOk h0' (ArgsKeep.refl na s₀'); rwa [est, e4, ← q₀, ← qa 2 (by omega), ← qa 3 (by omega)] at this
  have hwD : Covers [⟨State.addr (arg s₀ 2), (arg s₀ 3).toNat⟩] s₀.wr := by
    rw [h0.2.1]; exact covers_of_mem (by simp)
  have hwD' : Covers [⟨State.addr (arg s₀ 2), (arg s₀ 3).toNat⟩] s₀'.wr := by
    rw [h0'.2.1, qa 2 (by omega), qa 3 (by omega)]; exact covers_of_mem (by simp)
  have hcD' : (⟨State.addr (s₀.gpr .r0), 256⟩ : Region).Disjoint ⟨State.addr (arg s₀ 2), (arg s₀ 3).toNat⟩ := by
    rw [q₁, qa 2 (by omega), qa 3 (by omega)]; exact h0'.2.2.1
  have hA := one_argsCr h0
  have hA' : ∀ r ∈ crFrame (oSt s₀) (arg s₀ 4) s₀.sp (arg s₀ 2) (arg s₀ 3).toNat, (args s₀' na).Disjoint r := by
    have := one_argsCr h0'; rwa [est, e4, ← q₀, ← qa 2 (by omega), ← qa 3 (by omega)] at this
  have x2 := rel_wp (F := D1 s₀) (F' := D1 s₀') (G := OF na s₀ s₀) (G' := OF na s₀ s₀')
    (rel_of_ct (crypt_ct L (k8 := BitVec.ofNat 32 (s₀.gpr .r1).toNat) (R := (s₀.gpr .r1).toNat) (D := arg s₀ 2)
        (n := (arg s₀ 3).toNat) (q := 0))
      (fun s h => (cr_wpI L spf hd hwD h0.2.2.1 hA hR h.1 h.2.1 (by rw [h.2.2.1]; simp) h.2.2.2).1)
      (fun s h => (cr_wpI L spf' hd' hwD' hcD' hA' hR h.1 h.2.1 (by rw [h.2.2.1]; simp) h.2.2.2).1))
    (fun s h => (cr_wpI L spf hd hwD h0.2.2.1 hA hR h.1 h.2.1 (by rw [h.2.2.1]; simp) h.2.2.2).2)
    (fun s h => (cr_wpI L spf' hd' hwD' hcD' hA' hR h.1 h.2.1 (by rw [h.2.2.1]; simp) h.2.2.2).2)
  exact x1.seq x2

theorem oneTag_rel {o : Nat} (ho : o = 0 ∨ o = 112) :
    RelCT isa (fun a b => OF na s₀ s₀ a ∧ OF na s₀ s₀' b) (oneTag o)
      fun a b => OF na s₀ s₀ a ∧ OF na s₀ s₀' b := by
  obtain ⟨q₀, q₁, q₂, q₃, q₄, qa⟩ := hq
  have L := oneLay h0
  have spf := h0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have spf' := h0'.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hR : roundsOk s₀ := h0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hin : args s₀ na ∈ s₀.rd := by rw [h0.1]; simp
  have hin' : args s₀' na ∈ s₀'.rd := by rw [h0'.1]; simp
  have e4 : arg s₀' 4 = arg s₀ 4 := (qa 4 (by omega)).symm
  have est : oSt s₀' = oSt s₀ := by show arg s₀' 4 + _ = arg s₀ 4 + _; rw [e4]
  have hJ := one_argsJ0 h0
  have hJ' : ∀ r ∈ j0Frame (oSt s₀) (arg s₀ 4) s₀.sp, (args s₀' na).Disjoint r := by
    have := one_argsJ0 h0'; rwa [est, e4, ← q₀] at this
  have hT := disj_sub (one_argsOt h0 ho) tag_otSub
  have hT' : ∀ r ∈ tagFrame (oSt s₀) (arg s₀ 4) s₀.sp o, (args s₀' na).Disjoint r := by
    have := disj_sub (one_argsOt h0' ho) tag_otSub; rwa [est, e4, ← q₀] at this
  have ag : RelCT isa (fun a b => OF na s₀ s₀ a ∧ OF na s₀ s₀' b) (.block dataArgs) fun _ _ => True :=
    argsR hn q₀ spf qa (one_hw h0) (one_hw h0') ⟨_, by taint_decide⟩ (fun s h => h.choose_spec.2)
      (fun s h => h.choose_spec.2)
  let D1 : State → State → Prop := fun t₀ s => OF na s₀ t₀ s ∧ s.gpr .r4 = arg s₀ 2 ∧
    s.gpr .r5 = arg s₀ 3 ∧ s.gpr .r6 = BitVec.ofNat 32 0
  have x1 := rel_wp (F := OF na s₀ s₀) (F' := OF na s₀ s₀') (G := D1 s₀) (G' := D1 s₀') ag
    (fun s h => da_wpI spf hin hn h)
    (fun s h => WP.mono (da_wpI spf' hin' hn h) fun s' ⟨y₁, y₂, y₃, y₄⟩ =>
      ⟨y₁, by rw [y₂, qa 2 (by omega)], by rw [y₃, qa 3 (by omega)], y₄⟩)
  have hd := one_dataOk h0 (ArgsKeep.refl na s₀)
  have hd' : DataOk (oSt s₀) (arg s₀ 4) s₀.sp s₀' (arg s₀ 2) (arg s₀ 3).toNat := by
    have := one_dataOk h0' (ArgsKeep.refl na s₀'); rwa [est, e4, ← q₀, ← qa 2 (by omega), ← qa 3 (by omega)] at this
  have x2 := rel_wp (F := D1 s₀) (F' := D1 s₀') (G := OF na s₀ s₀) (G' := OF na s₀ s₀')
    (rel_of_ct (absorb_ct L (yo := 16) (.inr rfl) (D := arg s₀ 2) (n := (arg s₀ 3).toNat) (q := 0) (by decide))
      (fun s h => (abs_wpI L spf hJ hd h.1 h.2.1 (by rw [h.2.2.1]; simp) h.2.2.2).1)
      (fun s h => (abs_wpI L spf' hJ' hd' h.1 h.2.1 (by rw [h.2.2.1]; simp) h.2.2.2).1))
    (fun s h => (abs_wpI L spf hJ hd h.1 h.2.1 (by rw [h.2.2.1]; simp) h.2.2.2).2)
    (fun s h => (abs_wpI L spf' hJ' hd' h.1 h.2.1 (by rw [h.2.2.1]; simp) h.2.2.2).2)
  let B3 : State → State → Prop := fun t₀ s => OF na s₀ t₀ s ∧
    s.gpr .r6 = BitVec.ofNat 32 ((arg s₀ 3).toNat % 16)
  have x3 := rel_wp (F := OF na s₀ s₀) (F' := OF na s₀ s₀') (G := B3 s₀) (G' := B3 s₀')
    (argsR hn q₀ spf qa (one_hw h0) (one_hw h0') ⟨_, by taint_decide⟩ (fun s h => h.choose_spec.2)
      (fun s h => h.choose_spec.2))
    (fun s h => b3_wpI spf hin hn h)
    (fun s h => WP.mono (b3_wpI spf' hin' hn h) fun s' ⟨y₁, y₂⟩ => ⟨y₁, by rw [y₂, qa 3 (by omega)]⟩)
  have x4 := rel_wp (F := B3 s₀) (F' := B3 s₀') (G := OF na s₀ s₀) (G' := OF na s₀ s₀')
    (rel_of_ct (flush_ct L (yo := 16) (.inr rfl) (q := (arg s₀ 3).toNat % 16) (Nat.mod_lt _ (by decide)))
      (fun s ⟨⟨k7, he, _⟩, h6⟩ => ⟨k7, _, he, h6⟩) (fun s ⟨⟨k7, he, _⟩, h6⟩ => ⟨k7, _, he, h6⟩))
    (fun s h => fl_wpI L spf hJ (Nat.mod_lt _ (by decide)) h.1 h.2)
    (fun s h => fl_wpI L spf' hJ' (Nat.mod_lt _ (by decide)) h.1 h.2)
  have x5 := rel_wp (F := OF na s₀ s₀) (F' := OF na s₀ s₀') (G := OF na s₀ s₀) (G' := OF na s₀ s₀')
    (argsR hn q₀ spf qa (one_hw h0) (one_hw h0') ⟨_, by taint_decide⟩ (fun s h => h.choose_spec.2)
      (fun s h => h.choose_spec.2))
    (fun s h => b4_wpI spf hin hn h) (fun s h => b4_wpI spf' hin' hn h)
  have x6 := rel_wp (F := OF na s₀ s₀) (F' := OF na s₀ s₀') (G := OF na s₀ s₀) (G' := OF na s₀ s₀')
    (rel_of_ct (tag_ct L ho hR) (fun s ⟨k7, he, _⟩ => ⟨k7, he⟩) (fun s ⟨k7, he, _⟩ => ⟨k7, he⟩))
    (fun s h => tg_wpI L spf ho hT hR h) (fun s h => tg_wpI L spf' ho hT' hR h)
  exact x1.seq (x2.seq (x3.seq (x4.seq (x5.seq x6))))

end

end VG.Proof.AesGcm.Arm
