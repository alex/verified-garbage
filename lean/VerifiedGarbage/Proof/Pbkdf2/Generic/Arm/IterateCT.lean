import VerifiedGarbage.Proof.Pbkdf2.Generic.Arm.Iterate

/-!
# PBKDF2-HMAC over any streaming hash function on 32-bit ARM: `iterate`, constant time

Untrusted: everything here is checked by Lean. As on AArch64
(`Proof/Pbkdf2/Generic/AArch64/IterateCT.lean`); the prologue loads
`scratch` from the stack, so its taint check starts with the stack argument
public (`argTaint`).
-/

namespace VG.Proof.Pbkdf2.Generic.Arm

open VG.Arm
open VG.Impl.Hmac.Generic.Arm (Hash copy scrAt)
open VG.Impl.Pbkdf2.Generic.Arm (stO tmpO uO xorLoop count2 atSt body prologue iterate)
open VG.Proof.MdStream.Arm (eval_eq eval_ne)
open VG.Proof.Hmac.Generic.Arm

/-- The argument registers. -/
abbrev args : List Reg := [.r0, .r1, .r2, .r3]

/-- The registers `KR` fixes that the code between the calls uses. -/
abbrev pubRegs : List Reg := [.r4, .r5, .r6, .r11]

/-- The block that sets up a call of `update` on the state, with `D` bytes at `scratch + o`. -/
abbrev updBlock (H : Hash) (o : Nat) : List Instr :=
  atSt H ++ scrAt .r1 o ++ [.movw .r7 (BitVec.ofNat 16 H.D), .mov .r10 (.reg .r11),
    .movw .r2 (BitVec.ofNat 16 H.B), .mov .r3 (.imm 0)]

/-- The block that sets up a call of `finalize` on the state, into `scratch + o`. -/
abbrev finBlock (H : Hash) (o : Nat) : List Instr :=
  atSt H ++ count2 H ++ scrAt .r1 o ++ [.mov .r12 (.reg .r11)]

theorem skip_check : ∃ hc, (VG.Taint.check taint (Taint.ofRegs []) (.block []) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem cmp_check : ∃ hc, (VG.Taint.check taint (Taint.ofRegs pubRegs) (.block [.cmp .r6 (.imm 0)]) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem dec_check :
    ∃ hc, (VG.Taint.check taint (Taint.ofRegs pubRegs) (.block [.subs .r6 .r6 (.imm 1)]) hc).isSome = true :=
  ⟨_, by taint_decide⟩

/-- The taint checks of the pieces of `iterate` between its calls. -/
structure Checks (H : Hash) : Prop where
  pro : ∃ hc, (VG.Taint.check taint (argTaint args 4) (.block (prologue H)) hc).isSome = true
  copyU : ∃ hc,
    (VG.Taint.check taint (Taint.ofRegs (.r1 :: pubRegs)) (copy .r1 0 .r11 (uO H) H.D) hc).isSome = true
  copyK : ∀ o ∈ [0, H.S], ∃ hc,
    (VG.Taint.check taint (Taint.ofRegs pubRegs) (copy .r4 o .r11 (stO H) H.S) hc).isSome = true
  upd : ∀ o ∈ [uO H, tmpO H], ∃ hc,
    (VG.Taint.check taint (Taint.ofRegs pubRegs) (.block (updBlock H o)) hc).isSome = true
  fin : ∀ o ∈ [uO H, tmpO H], ∃ hc,
    (VG.Taint.check taint (Taint.ofRegs pubRegs) (.block (finBlock H o)) hc).isSome = true
  xor : ∃ hc, (VG.Taint.check taint (Taint.ofRegs pubRegs) (xorLoop H) hc).isSome = true
  restore : ∃ hc, (VG.Taint.check taint (Taint.ofRegs pubRegs) (.block H.restore) hc).isSome = true

/-- The public arguments are the same. -/
structure PubEq (s₀ s₀' : State) : Prop where
  sp : s₀.sp = s₀'.sp
  r0 : s₀.gpr .r0 = s₀'.gpr .r0
  r1 : s₀.gpr .r1 = s₀'.gpr .r1
  r2 : s₀.gpr .r2 = s₀'.gpr .r2
  r3 : s₀.gpr .r3 = s₀'.gpr .r3
  a0 : stackArg s₀ 0 = stackArg s₀' 0

variable {H : Hash} (hH : HashOK H) {sc : Nat}
variable {s₀ s₀' : State} (hp : Pre (H := H) sc s₀) (hp' : Pre (H := H) sc s₀') (hq : PubEq s₀ s₀')

theorem PubEq.nn (hq : PubEq s₀ s₀') : Generic.Arm.nn s₀ = Generic.Arm.nn s₀' := by
  show (s₀.gpr .r2).toNat = (s₀'.gpr .r2).toNat; rw [hq.r2]

theorem kr_agree (hq : PubEq s₀ s₀') {m : Nat} {s s' : State} (h : KR (H := H) sc s₀ m s)
    (h' : KR (H := H) sc s₀' m s') : ∀ r ∈ pubRegs, s.gpr r = s'.gpr r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [h.r4, h'.r4, key, key, hq.r0]
  · rw [h.r5, h'.r5, tp, tp, hq.r3]
  · rw [h.r6, h'.r6]
  · rw [h.r11, h'.r11, scr, scr, hq.a0]

theorem eqs (hq : PubEq s₀ s₀') : scr s₀' = scr s₀ ∧ ∀ o : Nat, sO s₀' o = sO s₀ o :=
  ⟨hq.a0.symm, fun o => by rw [sO, sO, scr, scr, hq.a0]⟩

/-- The stack argument lies outside the writable regions. -/
theorem args_wf {t : State} (h : Pre (H := H) sc t) :
    t.sp.toNat + 4 ≤ 2 ^ 32 ∧ ∀ r ∈ t.wr, Region.Disjoint ⟨State.addr t.sp, 4⟩ r := by
  have e : (⟨State.addr t.sp, 4⟩ : Region) = argR t := by simp [stackArgAddr]
  refine ⟨h.spf, ?_⟩
  simp only [e, h.wr, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact h.a_t
  · exact h.a_s

include hH hp hp' hq

omit hH in
/-- A piece of code between calls that keeps `KR`. -/
theorem kr_rel {m : Nat} {c : Prog isa}
    (hck : ∃ hc, (VG.Taint.check taint (Taint.ofRegs pubRegs) c hc).isSome = true)
    (hw : ∀ {t₀ : State}, Pre (H := H) sc t₀ → ∀ s, KR (H := H) sc t₀ m s → WP isa c s (KR (H := H) sc t₀ m)) :
    RelCT isa (fun s s' => KR (H := H) sc s₀ m s ∧ KR (H := H) sc s₀' m s') c
      fun s s' => KR (H := H) sc s₀ m s ∧ KR (H := H) sc s₀' m s' :=
  rel_taint pubRegs (fun _ _ h h' => kr_agree hq h h') hck (hw hp) (hw hp')

theorem upd_rel' {m : Nat} {o : Nat} (ho : o = uO H ∨ o = tmpO H) (hc : Checks H) :
    RelCT isa (fun s s' => KR (H := H) sc s₀ m s ∧ KR (H := H) sc s₀' m s')
      (H.callUpd (atSt H) H.B o H.D)
      fun s s' => KR (H := H) sc s₀ m s ∧ KR (H := H) sc s₀' m s' := by
  obtain ⟨e2, e3⟩ := eqs hq
  have ha := rel_taint (G := fun t => KR (H := H) sc s₀ m t ∧
      UpdArgs hH t (sO s₀ (stO H)) (sO s₀ o) (scr s₀) H.D ∧ count t = BitVec.ofNat 64 H.B)
    (G' := fun t => KR (H := H) sc s₀' m t ∧
      UpdArgs hH t (sO s₀ (stO H)) (sO s₀ o) (scr s₀) H.D ∧ count t = BitVec.ofNat 64 H.B)
    pubRegs (fun _ _ h h' => kr_agree hq h h') (hc.upd o (by rcases ho with rfl | rfl <;> simp))
    (fun s h => WP.mono (updArgs_ok hH hp h ho) fun _ ⟨k, a, x1, _⟩ => ⟨k, a, x1⟩)
    (fun s h => WP.mono (updArgs_ok hH hp' h ho) fun _ ⟨k, a, x1, _⟩ =>
      ⟨k, e3 (stO H) ▸ e3 o ▸ e2 ▸ a, x1⟩)
  exact ha.seq (rel_wp (upd_rel hH (sp := s₀.sp) (st := sO s₀ (stO H)) (d := sO s₀ o) (sc := scr s₀)
    (len := H.D) fun s s' ⟨⟨k, a, x1⟩, ⟨k', a', x1'⟩⟩ => ⟨a, a', by rw [x1, x1'], k.sp, by rw [k'.sp, hq.sp]⟩)
    (fun _ ⟨k, a, _⟩ => updCall_ok hH hp k ho a fun _ k' _ _ => k')
    (fun _ ⟨k, a, _⟩ => updCall_ok hH hp' k ho ((e3 (stO H)).symm ▸ (e3 o).symm ▸ e2.symm ▸ a)
      fun _ k' _ _ => k'))

theorem fin_rel' {m : Nat} {o : Nat} (ho : o = uO H ∨ o = tmpO H) (hc : Checks H) :
    RelCT isa (fun s s' => KR (H := H) sc s₀ m s ∧ KR (H := H) sc s₀' m s')
      (H.callFin (atSt H) (count2 H) o)
      fun s s' => KR (H := H) sc s₀ m s ∧ KR (H := H) sc s₀' m s' := by
  obtain ⟨e2, e3⟩ := eqs hq
  have ha := rel_taint (G := fun t => KR (H := H) sc s₀ m t ∧
      FinArgs hH t (sO s₀ (stO H)) (sO s₀ o) (scr s₀) ∧ count t = BitVec.ofNat 64 (H.B + H.D))
    (G' := fun t => KR (H := H) sc s₀' m t ∧
      FinArgs hH t (sO s₀ (stO H)) (sO s₀ o) (scr s₀) ∧ count t = BitVec.ofNat 64 (H.B + H.D))
    pubRegs (fun _ _ h h' => kr_agree hq h h') (hc.fin o (by rcases ho with rfl | rfl <;> simp))
    (fun s h => WP.mono (finArgs_ok hH hp h ho) fun _ ⟨k, a, x1, _⟩ => ⟨k, a, x1⟩)
    (fun s h => WP.mono (finArgs_ok hH hp' h ho) fun _ ⟨k, a, x1, _⟩ =>
      ⟨k, e3 (stO H) ▸ e3 o ▸ e2 ▸ a, x1⟩)
  exact ha.seq (rel_wp (fin_rel hH (sp := s₀.sp) (st := sO s₀ (stO H)) (o := sO s₀ o) (sc := scr s₀)
    fun s s' ⟨⟨k, a, x1⟩, ⟨k', a', x1'⟩⟩ => ⟨a, a', by rw [x1, x1'], k.sp, by rw [k'.sp, hq.sp]⟩)
    (fun _ ⟨k, a, _⟩ => finCall_ok hH hp k ho a fun _ k' _ _ => k')
    (fun _ ⟨k, a, _⟩ => finCall_ok hH hp' k ho ((e3 (stO H)).symm ▸ (e3 o).symm ▸ e2.symm ▸ a)
      fun _ k' _ _ => k'))

theorem body_rel (hc : Checks H) {m : Nat} (hm : 1 ≤ m) (hn : m < 2 ^ 32) :
    RelCT isa (fun s s' => KR (H := H) sc s₀ m s ∧ KR (H := H) sc s₀' m s') (body H)
      fun s s' => KR (H := H) sc s₀ (m - 1) s ∧ KR (H := H) sc s₀' (m - 1) s' := by
  have ck : ∀ {o : Nat}, (o = 0 ∨ o = H.S) → RelCT isa (fun s s' => KR (H := H) sc s₀ m s ∧ KR (H := H) sc s₀' m s')
      (copy .r4 o .r11 (stO H) H.S) fun s s' => KR (H := H) sc s₀ m s ∧ KR (H := H) sc s₀' m s' :=
    fun ho => kr_rel hp hp' hq (m := m) (hc.copyK _ (by rcases ho with rfl | rfl <;> simp))
      fun hp s k => WP.mono (copyKey_ok hH hp k ho) fun _ h => h.1
  have x := kr_rel hp hp' hq (m := m) hc.xor fun hp s k => WP.mono (xor'_ok hp k) fun _ h => h.1
  have d := rel_taint (G := KR (H := H) sc s₀ (m - 1)) (G' := KR (H := H) sc s₀' (m - 1)) pubRegs
    (fun _ _ h h' => kr_agree hq h h') dec_check
    (fun s k => WP.mono (dec_ok hm hn k) fun _ h => h.1) (fun s k => WP.mono (dec_ok hm hn k) fun _ h => h.1)
  exact (ck (.inl rfl)).seq ((upd_rel' hH hp hp' hq (.inl rfl) hc).seq ((fin_rel' hH hp hp' hq (.inr rfl) hc).seq
    ((ck (.inr rfl)).seq ((upd_rel' hH hp hp' hq (.inr rfl) hc).seq ((fin_rel' hH hp hp' hq (.inl rfl) hc).seq
    (x.seq d))))))

/-- The loop's invariant in two runs, with `n` steps left. -/
abbrev LoopInv (n : Nat) (s s' : State) : Prop :=
  1 ≤ n ∧ n ≤ nn s₀ ∧ Inv hH sc s₀ n s ∧ Inv hH sc s₀' n s'

theorem step_rel (hc : Checks H) (n : Nat) :
    RelCT isa (LoopInv hH (sc := sc) (s₀ := s₀) (s₀' := s₀') n) (body H) fun s s' =>
      isa.eval .ne s = isa.eval .ne s' ∧
      (isa.eval .ne s = some false → Inv hH sc s₀ 0 s ∧ Inv hH sc s₀' 0 s') ∧
      (isa.eval .ne s = some true → ∃ m < n, LoopInv hH (sc := sc) (s₀ := s₀) (s₀' := s₀') m s s') := by
  have hlt := nn_lt (s₀ := s₀)
  by_cases hn : 1 ≤ n ∧ n ≤ nn s₀
  · have b := (body_rel hH hp hp' hq hc hn.1 (by omega)).mono (P' := LoopInv hH (sc := sc) (s₀ := s₀) (s₀' := s₀') n)
      (fun _ _ (h : LoopInv hH (sc := sc) (s₀ := s₀) (s₀' := s₀') n _ _) => ⟨h.2.2.1.kr, h.2.2.2.kr⟩)
      fun _ _ h => h
    refine (b.wp (F₁ := fun (t : State) => Inv hH sc s₀ (n - 1) t ∧ t.z = decide (n - 1 = 0))
      (F₂ := fun (t : State) => Inv hH sc s₀' (n - 1) t ∧ t.z = decide (n - 1 = 0))
      fun s s' (h : LoopInv hH (sc := sc) (s₀ := s₀) (s₀' := s₀') n _ _) =>
        ⟨body_ok hH hp hn.1 (by omega) h.2.2.1, body_ok hH hp' hn.1 (by omega) h.2.2.2⟩).mono
      (fun _ _ h => h) fun t t' h => ?_
    obtain ⟨_, ⟨i, z⟩, ⟨i', z'⟩⟩ := h
    have e : isa.eval .ne t = some (!decide (n - 1 = 0)) := by show eval .ne t = _; rw [eval_ne, z]
    have e' : isa.eval .ne t' = some (!decide (n - 1 = 0)) := by show eval .ne t' = _; rw [eval_ne, z']
    rw [e, e']
    refine ⟨rfl, fun hf => ?_, fun ht => ?_⟩
    · have hl : n - 1 = 0 := by simpa using hf
      exact ⟨hl ▸ i, hl ▸ i'⟩
    · have hl : n - 1 ≠ 0 := by simpa using ht
      exact ⟨n - 1, by omega, by omega, by omega, i, i'⟩
  · intro _ _ _ _ _ _ h
    exact absurd ⟨h.1, h.2.1⟩ hn

theorem loop_rel (hc : Checks H) :
    RelCT isa (fun s s' => (Inv hH sc s₀ (nn s₀) s ∧ s.z = decide (nn s₀ = 0)) ∧
        (Inv hH sc s₀' (nn s₀') s' ∧ s'.z = decide (nn s₀' = 0)))
      (.ite .eq (.block []) (.loop (body H) .ne))
      fun s s' => Inv hH sc s₀ 0 s ∧ Inv hH sc s₀' 0 s' := by
  have hN := hq.nn
  have ev : ∀ {t : State} {k : Nat}, t.z = decide (k = 0) → isa.eval .eq t = some (decide (k = 0)) :=
    fun h => by show eval .eq _ = _; rw [eval_eq, h]
  refine RelCT.ite (fun s s' h => by rw [ev h.1.2, ev h.2.2, hN]) ?_ ?_
  · by_cases e : nn s₀ = 0
    · have e' : nn s₀' = 0 := hN ▸ e
      exact (rel_taint (c := .block []) (F := fun s => Inv hH sc s₀ (nn s₀) s ∧ s.z = decide (nn s₀ = 0))
        (F' := fun s => Inv hH sc s₀' (nn s₀') s ∧ s.z = decide (nn s₀' = 0))
        (G := Inv hH sc s₀ 0) (G' := Inv hH sc s₀' 0) []
        (fun s s' h h' => by simp) skip_check
        (fun s h => WP.block_nil (e ▸ h.1)) (fun s h => WP.block_nil (e' ▸ h.1))).mono (fun _ _ h => h.1)
        fun _ _ h => h
    · intro _ _ _ _ _ _ h
      have z := h.2
      rw [ev h.1.1.2] at z
      exact absurd (by simpa using z) e
  · refine (RelCT.loop (M := isa) (LoopInv hH (sc := sc) (s₀ := s₀) (s₀' := s₀')) (step_rel hH hp hp' hq hc)
      (nn s₀)).mono (fun s s' h => ?_) fun _ _ h => h
    have z := h.2
    rw [ev h.1.1.2] at z
    have e : nn s₀ ≠ 0 := by simpa using z
    exact ⟨by omega, (Nat.le_refl _), h.1.1.1, hN ▸ h.1.2.1⟩

theorem ct (hc : Checks H) : RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') (iterate H) fun _ _ => True := by
  have hN := hq.nn
  have pro := rel_agree (F := fun s => s = s₀) (F' := fun s => s = s₀')
    (G := fun s => KR (H := H) sc s₀ (nn s₀) s ∧ s.gpr .r1 = up s₀ ∧ Frame [saveR H (scr s₀)] s₀.mem s.mem)
    (G' := fun s => KR (H := H) sc s₀' (nn s₀') s ∧ s.gpr .r1 = up s₀' ∧ Frame [saveR H (scr s₀')] s₀'.mem s.mem)
    (argTaint args 4) (fun s s' e e' => by
        rw [e, e']
        refine agree_argTaint (fun r hr => ?_) hq.sp (args_wf hp) (args_wf hp')
          (argMem_of (j := 1) hq.sp hp.spf fun i hi => by rw [show i = 0 by omega]; exact hq.a0)
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact hq.r0
        · exact hq.r1
        · exact hq.r2
        · exact hq.r3) hc.pro
    (fun _ e => by rw [e]; exact pro_ok hp) (fun _ e => by rw [e]; exact pro_ok hp')
  have cu := rel_taint
    (F := fun s => KR (H := H) sc s₀ (nn s₀) s ∧ s.gpr .r1 = up s₀ ∧ Frame [saveR H (scr s₀)] s₀.mem s.mem)
    (F' := fun s => KR (H := H) sc s₀' (nn s₀') s ∧ s.gpr .r1 = up s₀' ∧ Frame [saveR H (scr s₀')] s₀'.mem s.mem)
    (G := Inv hH sc s₀ (nn s₀)) (G' := Inv hH sc s₀' (nn s₀')) (.r1 :: pubRegs)
    (fun s s' h h' r hm => by
      rcases List.mem_cons.mp hm with rfl | hm
      · rw [h.2.1, h'.2.1, up, up, hq.r1]
      · exact kr_agree hq h.1 (hN ▸ h'.1) r hm) hc.copyU
    (fun s h => copyU_ok hH hp h.1 h.2.1 h.2.2) (fun s h => copyU_ok hH hp' h.1 h.2.1 h.2.2)
  have cm := rel_taint (F := Inv hH sc s₀ (nn s₀)) (F' := Inv hH sc s₀' (nn s₀'))
    (G := fun s => Inv hH sc s₀ (nn s₀) s ∧ s.z = decide (nn s₀ = 0))
    (G' := fun s => Inv hH sc s₀' (nn s₀') s ∧ s.z = decide (nn s₀' = 0)) pubRegs
    (fun s s' h h' => kr_agree hq h.kr (hN ▸ h'.kr)) cmp_check
    (fun s h => cmp_ok hH h) (fun s h => cmp_ok hH h)
  obtain ⟨_, hr⟩ := hc.restore
  have restore : RelCT isa (fun s s' => Inv hH sc s₀ 0 s ∧ Inv hH sc s₀' 0 s') (.block H.restore)
      fun _ _ => True :=
    RelCT.taint (A := taint) (Taint.ofRegs pubRegs) (fun _ _ h =>
      Taint.agree_ofRegs (kr_agree hq h.1.kr h.2.kr)) hr
  exact pro.seq (cu.seq (cm.seq ((loop_rel hH hp hp' hq hc).seq restore)))

end VG.Proof.Pbkdf2.Generic.Arm

namespace VG.Proof.Pbkdf2.Generic.Arm

open VG.Arm
open VG.Impl.Hmac.Generic.Arm (Hash)
open VG.Proof.Hmac.Generic.Arm

/-- `iterate` is verified against `iterG`, given the taint checks, which the
kernel evaluates for each hash function. -/
theorem verified {H : Hash} (hH : HashOK H) {sc : Nat} (hc : Checks H)
    (hfit : H.buf + H.S + 2 * H.F ≤ 8 * sc) (hsat : ∃ s, (iterG hH.SH sc).pre s) :
    Verified Arm.target (VG.Impl.Pbkdf2.Generic.Arm.iterate H) (iterG hH.SH sc) := by
  refine ⟨fun s hs => correct hH (pre_of hH sc hs hfit), fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, hsat⟩
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hpub
  exact (ct hH (pre_of hH sc h₁ hfit) (pre_of hH sc h₂ hfit) ⟨h1, h2, h3, h4, h5, h6⟩ hc
    _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.Pbkdf2.Generic.Arm
