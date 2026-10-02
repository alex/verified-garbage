import VerifiedGarbage.Proof.Pbkdf2.Generic.X86.Iterate

/-!
# PBKDF2-HMAC over any streaming hash function on x86 (32-bit): `iterate`, constant time

As on 32-bit ARM (`Proof/Pbkdf2/Generic/Arm/Instances.lean`): the pieces
between the calls are checked by the taint analysis, those that read the
arguments on the stack (the prologue, and the loads of `key` and `t`) with the
arguments public (`argTaint`); the calls are related by `upd_rel` and
`fin_rel`.
-/

namespace VG.Proof.Pbkdf2.Generic.X86

open VG.X86
open VG.Impl.Hmac.Generic.X86 (Hash copy at_)
open VG.Impl.Pbkdf2.Generic.X86 (stO tmpO uO xorLoop atSt ldKey ldT body prologue iterate)
open VG.Proof.Sha256.X86.Stream (eval_e eval_ne)
open VG.Proof.Hmac.Generic.X86

/-- The registers `KR` fixes. -/
abbrev pubRegs : List Reg := [.esp, .ebp, .edi]

theorem skip_check : ∃ hc, (VG.Taint.check taint (τr []) (.block []) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem test_check : ∃ hc, (VG.Taint.check taint (τr pubRegs) (.block [.alu .test .edi (.reg .edi)]) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem dec_check :
    ∃ hc, (VG.Taint.check taint (τr pubRegs) (.block [.alu .sub .edi (.imm 1)]) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem ld_check {i : Nat} (hi : i = 0 ∨ i = 3) : ∃ hc, (VG.Taint.check taint (argTaint [.ebp, .edi] (4 + 4 * 5))
    (.block [.mov .esi (.mem (at_ .esp (4 + 4 * i)))]) hc).isSome = true := by
  rcases hi with rfl | rfl <;> exact ⟨_, by taint_decide⟩

/-- The taint checks of the pieces of `iterate` between its calls. -/
structure Checks (H : Hash) : Prop where
  pro : ∃ hc, (VG.Taint.check taint (argTaint [] (4 + 4 * 5)) (.block (prologue H)) hc).isSome = true
  copyU : ∃ hc,
    (VG.Taint.check taint (τr (.esi :: pubRegs)) (copy .esi 0 .ebp (uO H) H.D) hc).isSome = true
  copyK : ∀ o ∈ [0, H.S], ∃ hc,
    (VG.Taint.check taint (τr (.esi :: pubRegs)) (copy .esi o .ebp (stO H) H.S) hc).isSome = true
  upd : ∀ o ∈ [uO H, tmpO H], ∃ hc,
    (VG.Taint.check taint (τr pubRegs) (.block (updBlock H o)) hc).isSome = true
  fin : ∀ o ∈ [uO H, tmpO H], ∃ hc,
    (VG.Taint.check taint (τr pubRegs) (.block (finBlock H o)) hc).isSome = true
  xor : ∃ hc, (VG.Taint.check taint (τr (.esi :: pubRegs)) (xorLoop H) hc).isSome = true
  restore : ∃ hc, (VG.Taint.check taint (τr pubRegs) (.block H.restore) hc).isSome = true

/-- The public arguments are the same. -/
structure PubEq (s₀ s₀' : State) : Prop where
  esp : s₀.gpr .esp = s₀'.gpr .esp
  args : ∀ i < 5, arg s₀ i = arg s₀' i

variable {H : Hash} (hH : HashOK H) {sc : Nat}
variable {s₀ s₀' : State} (hp : Pre (H := H) sc s₀) (hp' : Pre (H := H) sc s₀') (hq : PubEq s₀ s₀')

theorem PubEq.nn (hq : PubEq s₀ s₀') : Generic.X86.nn s₀ = Generic.X86.nn s₀' := by
  show (arg s₀ 2).toNat = (arg s₀' 2).toNat; rw [hq.args 2 (by decide)]

theorem kr_agree (hq : PubEq s₀ s₀') {m : Nat} {s s' : State} (h : KR (H := H) sc s₀ m s)
    (h' : KR (H := H) sc s₀' m s') : ∀ r ∈ pubRegs, s.gpr r = s'.gpr r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [h.esp, h'.esp, E, E, hq.esp]
  · rw [h.ebp, h'.ebp, scr, scr, hq.args 4 (by decide)]
  · rw [h.edi, h'.edi]

theorem esi_agree (hq : PubEq s₀ s₀') {m : Nat} {s s' : State} (h : KR (H := H) sc s₀ m s)
    (h' : KR (H := H) sc s₀' m s') {i : Nat} (hi : i < 5) (e : s.gpr .esi = arg s₀ i) (e' : s'.gpr .esi = arg s₀' i) :
    ∀ r ∈ .esi :: pubRegs, s.gpr r = s'.gpr r := by
  intro r hr
  rcases List.mem_cons.mp hr with rfl | hr
  · rw [e, e', hq.args i hi]
  · exact kr_agree hq h h' r hr

theorem eqs (hq : PubEq s₀ s₀') : scr s₀' = scr s₀ ∧ ∀ o : Nat, sO s₀' o = sO s₀ o :=
  ⟨(hq.args 4 (by decide)).symm, fun o => by rw [sO, sO, scr, scr, hq.args 4 (by decide)]⟩

/-- The arguments lie outside the writable regions. -/
theorem args_out {t : State} (h : Pre (H := H) sc t) {s : State} (hsp : s.gpr .esp = E t) (hwr : s.wr = t.wr) :
    ArgsOut 5 s := by
  have e : (⟨(s.gpr .esp).setWidth 64, 4 + 4 * 5⟩ : Region) = ⟨(E t).setWidth 64, 4 + 20⟩ := by rw [hsp]
  refine ⟨by rw [hsp]; exact h.spf, ?_⟩
  rw [e, hwr, h.wr]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact Taint.frame_disjoint (by have := h.spf; omega) h.r_t h.a_t
  · exact Taint.frame_disjoint (by have := h.spf; omega) h.r_s h.a_s

include hH hp hp' hq

omit hH in
/-- A piece of code between calls that keeps `KR`. -/
theorem kr_rel {m : Nat} {c : Prog isa}
    (hck : ∃ hc, (VG.Taint.check taint (τr pubRegs) c hc).isSome = true)
    (hw : ∀ {t₀ : State}, Pre (H := H) sc t₀ → ∀ s, KR (H := H) sc t₀ m s → WP isa c s (KR (H := H) sc t₀ m)) :
    RelCT isa (fun s s' => KR (H := H) sc s₀ m s ∧ KR (H := H) sc s₀' m s') c
      fun s s' => KR (H := H) sc s₀ m s ∧ KR (H := H) sc s₀' m s' :=
  rel_agree (τr pubRegs) (fun _ _ h h' => agree_regs (kr_agree hq h h')) hck (hw hp) (hw hp')

omit hH in
/-- A load of `key` (`i = 0`) or `t` (`i = 3`) into `esi`. -/
theorem ld_rel {m : Nat} {i : Nat} (hi : i = 0 ∨ i = 3) :
    RelCT isa (fun s s' => KR (H := H) sc s₀ m s ∧ KR (H := H) sc s₀' m s')
      (.block [.mov .esi (.mem (at_ .esp (4 + 4 * i)))])
      fun s s' => (KR (H := H) sc s₀ m s ∧ s.gpr .esi = arg s₀ i) ∧
        (KR (H := H) sc s₀' m s' ∧ s'.gpr .esi = arg s₀' i) :=
  rel_agree (argTaint [.ebp, .edi] (4 + 4 * 5)) (fun s s' k k' =>
      agree_argTaint (fun r hr => kr_agree hq k k' r (by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; tauto))
        (kr_agree hq k k' .esp (by simp)) (args_out hp k.esp k.wr) (args_out hp' k'.esp k'.wr)
        fun j hj => by rw [k.argEq hp hj, k'.argEq hp' hj, hq.args j hj]) (ld_check hi)
    (fun _ k => WP.mono (ld_ok hp k hi) fun _ ⟨k₁, e, _⟩ => ⟨k₁, e⟩)
    (fun _ k => WP.mono (ld_ok hp' k hi) fun _ ⟨k₁, e, _⟩ => ⟨k₁, e⟩)

theorem upd_rel' {m : Nat} {o : Nat} (ho : o = uO H ∨ o = tmpO H) (hc : Checks H) :
    RelCT isa (fun s s' => KR (H := H) sc s₀ m s ∧ KR (H := H) sc s₀' m s')
      (H.callUpd (atSt H) .ebx .esi H.B o H.D)
      fun s s' => KR (H := H) sc s₀ m s ∧ KR (H := H) sc s₀' m s' := by
  obtain ⟨e2, e3⟩ := eqs hq
  have ha := rel_agree (G := fun t => KR (H := H) sc s₀ m t ∧
      UpdArgs hH t .esi .ebx (sO s₀ (stO H)) (sO s₀ o) (scr s₀) (BitVec.ofNat 32 H.B) H.D)
    (G' := fun t => KR (H := H) sc s₀' m t ∧
      UpdArgs hH t .esi .ebx (sO s₀ (stO H)) (sO s₀ o) (scr s₀) (BitVec.ofNat 32 H.B) H.D)
    (τr pubRegs) (fun _ _ h h' => agree_regs (kr_agree hq h h')) (hc.upd o (by rcases ho with rfl | rfl <;> simp))
    (fun s h => WP.mono (updArgs_ok hH hp h ho) fun _ ⟨k, a, _⟩ => ⟨k, a⟩)
    (fun s h => WP.mono (updArgs_ok hH hp' h ho) fun _ ⟨k, a, _⟩ =>
      ⟨k, e3 (stO H) ▸ e3 o ▸ e2 ▸ a⟩)
  exact ha.seq (rel_wp (upd_rel hH (sp := E s₀) fun s s' ⟨⟨k, a⟩, ⟨k', a'⟩⟩ =>
      ⟨a, a', k.esp, by rw [k'.esp, E, E, hq.esp]⟩)
    (fun _ ⟨k, a⟩ => updCall_ok hH hp k ho a fun _ k' _ _ => k')
    (fun _ ⟨k, a⟩ => updCall_ok hH hp' k ho ((e3 (stO H)).symm ▸ (e3 o).symm ▸ e2.symm ▸ a)
      fun _ k' _ _ => k'))

theorem fin_rel' {m : Nat} {o : Nat} (ho : o = uO H ∨ o = tmpO H) (hc : Checks H) :
    RelCT isa (fun s s' => KR (H := H) sc s₀ m s ∧ KR (H := H) sc s₀' m s')
      (H.callFin (atSt H) H.count2 .ebx o)
      fun s s' => KR (H := H) sc s₀ m s ∧ KR (H := H) sc s₀' m s' := by
  obtain ⟨e2, e3⟩ := eqs hq
  have ha := rel_agree (G := fun t => KR (H := H) sc s₀ m t ∧
      FinArgs hH t .ebx (sO s₀ (stO H)) (sO s₀ o) (scr s₀) (BitVec.ofNat 32 (H.B + H.D)) 0)
    (G' := fun t => KR (H := H) sc s₀' m t ∧
      FinArgs hH t .ebx (sO s₀ (stO H)) (sO s₀ o) (scr s₀) (BitVec.ofNat 32 (H.B + H.D)) 0)
    (τr pubRegs) (fun _ _ h h' => agree_regs (kr_agree hq h h')) (hc.fin o (by rcases ho with rfl | rfl <;> simp))
    (fun s h => WP.mono (finArgs_ok hH hp h ho) fun _ ⟨k, a, _⟩ => ⟨k, a⟩)
    (fun s h => WP.mono (finArgs_ok hH hp' h ho) fun _ ⟨k, a, _⟩ =>
      ⟨k, e3 (stO H) ▸ e3 o ▸ e2 ▸ a⟩)
  exact ha.seq (rel_wp (fin_rel hH (sp := E s₀) fun s s' ⟨⟨k, a⟩, ⟨k', a'⟩⟩ =>
      ⟨a, a', k.esp, by rw [k'.esp, E, E, hq.esp]⟩)
    (fun _ ⟨k, a⟩ => finCall_ok hH hp k ho a fun _ k' _ _ => k')
    (fun _ ⟨k, a⟩ => finCall_ok hH hp' k ho ((e3 (stO H)).symm ▸ (e3 o).symm ▸ e2.symm ▸ a)
      fun _ k' _ _ => k'))

theorem body_rel (hc : Checks H) {m : Nat} (hm : 1 ≤ m) (hn : m < 2 ^ 32) :
    RelCT isa (fun s s' => KR (H := H) sc s₀ m s ∧ KR (H := H) sc s₀' m s') (body H)
      fun s s' => KR (H := H) sc s₀ (m - 1) s ∧ KR (H := H) sc s₀' (m - 1) s' := by
  have ck : ∀ {o : Nat}, (o = 0 ∨ o = H.S) → RelCT isa (fun s s' => (KR (H := H) sc s₀ m s ∧ s.gpr .esi = arg s₀ 0) ∧
        (KR (H := H) sc s₀' m s' ∧ s'.gpr .esi = arg s₀' 0))
      (copy .esi o .ebp (stO H) H.S) fun s s' => KR (H := H) sc s₀ m s ∧ KR (H := H) sc s₀' m s' :=
    fun ho => rel_agree (τr (.esi :: pubRegs)) (fun _ _ h h' => agree_regs
        (esi_agree hq h.1 h'.1 (i := 0) (by decide) h.2 h'.2)) (hc.copyK _ (by rcases ho with rfl | rfl <;> simp))
      (fun s h => WP.mono (copyKey_ok hH hp h.1 h.2 ho) fun _ h => h.1)
      (fun s h => WP.mono (copyKey_ok hH hp' h.1 h.2 ho) fun _ h => h.1)
  have x : RelCT isa (fun s s' => (KR (H := H) sc s₀ m s ∧ s.gpr .esi = arg s₀ 3) ∧
        (KR (H := H) sc s₀' m s' ∧ s'.gpr .esi = arg s₀' 3))
      (xorLoop H) fun s s' => KR (H := H) sc s₀ m s ∧ KR (H := H) sc s₀' m s' :=
    rel_agree (τr (.esi :: pubRegs)) (fun _ _ h h' => agree_regs
        (esi_agree hq h.1 h'.1 (i := 3) (by decide) h.2 h'.2)) hc.xor
      (fun s h => WP.mono (xor'_ok hp h.1 h.2) fun _ h => h.1)
      (fun s h => WP.mono (xor'_ok hp' h.1 h.2) fun _ h => h.1)
  have d := rel_agree (G := KR (H := H) sc s₀ (m - 1)) (G' := KR (H := H) sc s₀' (m - 1)) (τr pubRegs)
    (fun _ _ h h' => agree_regs (kr_agree hq h h')) dec_check
    (fun s k => WP.mono (dec_ok hm hn k) fun _ h => h.1) (fun s k => WP.mono (dec_ok hm hn k) fun _ h => h.1)
  exact (ld_rel hp hp' hq (.inl rfl)).seq ((ck (.inl rfl)).seq ((upd_rel' hH hp hp' hq (.inl rfl) hc).seq
    ((fin_rel' hH hp hp' hq (.inr rfl) hc).seq ((ld_rel hp hp' hq (.inl rfl)).seq ((ck (.inr rfl)).seq
    ((upd_rel' hH hp hp' hq (.inr rfl) hc).seq ((fin_rel' hH hp hp' hq (.inl rfl) hc).seq
    ((ld_rel hp hp' hq (.inr rfl)).seq (x.seq d)))))))))

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
    refine (b.wp (F₁ := fun (t : State) => Inv hH sc s₀ (n - 1) t ∧ t.zf = some (decide (n - 1 = 0)))
      (F₂ := fun (t : State) => Inv hH sc s₀' (n - 1) t ∧ t.zf = some (decide (n - 1 = 0)))
      fun s s' (h : LoopInv hH (sc := sc) (s₀ := s₀) (s₀' := s₀') n _ _) =>
        ⟨body_ok hH hp hn.1 (by omega) h.2.2.1, body_ok hH hp' hn.1 (by omega) h.2.2.2⟩).mono
      (fun _ _ h => h) fun t t' h => ?_
    obtain ⟨_, ⟨i, z⟩, ⟨i', z'⟩⟩ := h
    have e : isa.eval .ne t = some (!decide (n - 1 = 0)) := by show eval .ne t = _; rw [eval_ne, z]; rfl
    have e' : isa.eval .ne t' = some (!decide (n - 1 = 0)) := by show eval .ne t' = _; rw [eval_ne, z']; rfl
    rw [e, e']
    refine ⟨rfl, fun hf => ?_, fun ht => ?_⟩
    · have hl : n - 1 = 0 := by simpa using hf
      exact ⟨hl ▸ i, hl ▸ i'⟩
    · have hl : n - 1 ≠ 0 := by simpa using ht
      exact ⟨n - 1, by omega, by omega, by omega, i, i'⟩
  · intro _ _ _ _ _ _ h
    exact absurd ⟨h.1, h.2.1⟩ hn

theorem loop_rel (hc : Checks H) :
    RelCT isa (fun s s' => (Inv hH sc s₀ (nn s₀) s ∧ s.zf = some (decide (nn s₀ = 0))) ∧
        (Inv hH sc s₀' (nn s₀') s' ∧ s'.zf = some (decide (nn s₀' = 0))))
      (.ite .e (.block []) (.loop (body H) .ne))
      fun s s' => Inv hH sc s₀ 0 s ∧ Inv hH sc s₀' 0 s' := by
  have hN := hq.nn
  have ev : ∀ {t : State} {k : Nat}, t.zf = some (decide (k = 0)) → isa.eval .e t = some (decide (k = 0)) :=
    fun h => by show eval .e _ = _; rw [eval_e, h]
  refine RelCT.ite (fun s s' h => by rw [ev h.1.2, ev h.2.2, hN]) ?_ ?_
  · by_cases e : nn s₀ = 0
    · have e' : nn s₀' = 0 := hN ▸ e
      exact (rel_agree (c := .block [])
        (F := fun s => Inv hH sc s₀ (nn s₀) s ∧ s.zf = some (decide (nn s₀ = 0)))
        (F' := fun s => Inv hH sc s₀' (nn s₀') s ∧ s.zf = some (decide (nn s₀' = 0)))
        (G := Inv hH sc s₀ 0) (G' := Inv hH sc s₀' 0) (τr [])
        (fun s s' h h' => agree_regs (by simp)) skip_check
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
    (G := fun s => KR (H := H) sc s₀ (nn s₀) s ∧ s.gpr .esi = up s₀ ∧ Frame [saveR H (scr s₀)] s₀.mem s.mem)
    (G' := fun s => KR (H := H) sc s₀' (nn s₀') s ∧ s.gpr .esi = up s₀' ∧ Frame [saveR H (scr s₀')] s₀'.mem s.mem)
    (argTaint [] (4 + 4 * 5)) (fun s s' e e' => by
        rw [e, e']
        exact agree_argTaint (fun r hr => nomatch hr) hq.esp (args_out hp rfl rfl) (args_out hp' rfl rfl)
          hq.args) hc.pro
    (fun _ e => by rw [e]; exact pro_ok hp) (fun _ e => by rw [e]; exact pro_ok hp')
  have cu := rel_agree
    (F := fun s => KR (H := H) sc s₀ (nn s₀) s ∧ s.gpr .esi = up s₀ ∧ Frame [saveR H (scr s₀)] s₀.mem s.mem)
    (F' := fun s => KR (H := H) sc s₀' (nn s₀') s ∧ s.gpr .esi = up s₀' ∧ Frame [saveR H (scr s₀')] s₀'.mem s.mem)
    (G := Inv hH sc s₀ (nn s₀)) (G' := Inv hH sc s₀' (nn s₀')) (τr (.esi :: pubRegs))
    (fun s s' h h' => agree_regs (esi_agree hq h.1 (hN ▸ h'.1) (i := 1) (by decide) h.2.1 h'.2.1)) hc.copyU
    (fun s h => copyU_ok hH hp h.1 h.2.1 h.2.2) (fun s h => copyU_ok hH hp' h.1 h.2.1 h.2.2)
  have cm := rel_agree (F := Inv hH sc s₀ (nn s₀)) (F' := Inv hH sc s₀' (nn s₀'))
    (G := fun s => Inv hH sc s₀ (nn s₀) s ∧ s.zf = some (decide (nn s₀ = 0)))
    (G' := fun s => Inv hH sc s₀' (nn s₀') s ∧ s.zf = some (decide (nn s₀' = 0))) (τr pubRegs)
    (fun s s' h h' => agree_regs (kr_agree hq h.kr (hN ▸ h'.kr))) test_check
    (fun s h => test_ok hH h) (fun s h => test_ok hH h)
  obtain ⟨_, hr⟩ := hc.restore
  have restore : RelCT isa (fun s s' => Inv hH sc s₀ 0 s ∧ Inv hH sc s₀' 0 s') (.block H.restore)
      fun _ _ => True :=
    RelCT.taint (A := taint) (τr pubRegs) (fun _ _ h => agree_regs (kr_agree hq h.1.kr h.2.kr)) hr
  exact pro.seq (cu.seq (cm.seq ((loop_rel hH hp hp' hq hc).seq restore)))

end VG.Proof.Pbkdf2.Generic.X86

namespace VG.Proof.Pbkdf2.Generic.X86

open VG.X86
open VG.Impl.Hmac.Generic.X86 (Hash)
open VG.Proof.Hmac.Generic.X86

/-- `iterate` is verified against `iterG`, given the taint checks, which the
kernel evaluates for each hash function. -/
theorem verified {H : Hash} (hH : HashOK H) {sc : Nat} (hc : Checks H)
    (hfit : H.buf + H.S + 2 * H.F ≤ 8 * sc) (hsat : ∃ s, (iterG hH.SH sc).pre s) :
    Verified X86.target (VG.Impl.Pbkdf2.Generic.X86.iterate H) (iterG hH.SH sc) := by
  refine ⟨fun s hs => correct hH (pre_of hH sc hs hfit), fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, hsat⟩
  obtain ⟨h1, h2⟩ := hpub
  exact (ct hH (pre_of hH sc h₁ hfit) (pre_of hH sc h₂ hfit) ⟨h1, h2⟩ hc
    _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-- The regions `iterate` reads and writes, of those `iterW` gives it. -/
def narrowRd (S D : Nat) (s : State) : List Region :=
  [⟨(arg s 0).setWidth 64, 2 * S⟩, ⟨(arg s 1).setWidth 64, D⟩, ⟨argAddr s 0, 20⟩]
def narrowWr (D sc : Nat) (s : State) : List Region :=
  [⟨(arg s 3).setWidth 64, D⟩, ⟨(arg s 4).setWidth 64, 8 * sc⟩]

/-- `iterate` is verified against `iterW`, which lets it write its arguments:
the code only reads them. -/
theorem verifiedW {H : Hash} (hH : HashOK H) {sc : Nat} (hc : Checks H)
    (hfit : H.buf + H.S + 2 * H.F ≤ 8 * sc) (hsat : ∃ s, (iterW hH.SH sc).pre s) :
    Verified X86.target (VG.Impl.Pbkdf2.Generic.X86.iterate H) (iterW hH.SH sc) := by
  have pre : ∀ s, (iterW hH.SH sc).pre s → (iterG hH.SH sc).pre
      (s.withRegions (narrowRd hH.SH.stateBytes hH.SH.digestBytes s) (narrowWr hH.SH.digestBytes sc s)) := by
    intro s h
    obtain ⟨_, _, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩ := h
    simp only [iterG, narrowRd, narrowWr, arg_withRegions, argAddr_withRegions, State.withRegions_gpr,
      State.withRegions_rd, State.withRegions_wr]
    exact ⟨trivial, trivial, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  refine Verified.narrowTo (verified hH hc hfit (hsat.elim fun s hs => ⟨_, pre s hs⟩))
    (narrowRd hH.SH.stateBytes hH.SH.digestBytes) (narrowWr hH.SH.digestBytes sc) pre (fun s h => ?_)
    (fun s h => ?_) (fun _ _ _ h => h) (fun _ _ _ _ h => h) hsat
  · obtain ⟨h1, h2, _⟩ := h
    rw [h1, h2]
    refine Covers.of_sub fun r hr => ?_
    simp only [narrowRd, narrowWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_append_left _ List.mem_cons_self, 0, by simp, by simp⟩
    · exact ⟨_, List.mem_append_left _ (List.mem_cons_of_mem _ List.mem_cons_self), 0, by simp, by simp⟩
    · exact ⟨_, List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)),
        0, by simp, by simp⟩
    · exact ⟨_, List.mem_append_right _ List.mem_cons_self, 0, by simp, by simp⟩
    · exact ⟨_, List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self), 0, by simp, by simp⟩
  · obtain ⟨_, h2, _⟩ := h
    rw [h2]
    refine Covers.of_sub fun r hr => ?_
    simp only [narrowWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self, 0, by simp, by simp⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, 0, by simp, by simp⟩

end VG.Proof.Pbkdf2.Generic.X86
