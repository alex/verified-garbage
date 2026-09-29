import VerifiedGarbage.Proof.Pbkdf2.Generic.AArch64.Iterate

/-!
# PBKDF2-HMAC over any streaming hash function on AArch64: `iterate`, constant time

Untrusted: everything here is checked by Lean. As on x86-64
(`Proof/Pbkdf2/Generic/X86_64/IterateCT.lean`).
-/

namespace VG.Proof.Pbkdf2.Generic.AArch64

open VG.AArch64
open VG.Impl.Hmac.Generic.AArch64 (Hash copy)
open VG.Impl.Pbkdf2.Generic.AArch64 (stO tmpO uO xorLoop count2 atSt body prologue main iterate)
open VG.Impl.Sha256.AArch64.Stream (mov)
open VG.Proof.MdStream.AArch64 (Upd)
open VG.Proof.Hmac.Generic.AArch64

/-- The arguments, once `n` is zero-extended. -/
abbrev args : List Reg := [.x0, .x1, .x2, .x3, .x4]

/-- The registers `KR` fixes that the code between the calls uses. -/
abbrev pubRegs : List Reg := [.x19, .x20, .x22, .x23]

/-- The block that sets up a call of `update` on the state, with `D` bytes at `scratch + o`. -/
abbrev updBlock (H : Hash) (o : Nat) : List Instr :=
  atSt H ++ [.movz .x .x1 (BitVec.ofNat 16 H.B) 0, .addImm .x .x2 .x23 o,
    .movz .x .x3 (BitVec.ofNat 16 H.D) 0, mov .x4 .x23]

/-- The block that sets up a call of `finalize` on the state, into `scratch + o`. -/
abbrev finBlock (H : Hash) (o : Nat) : List Instr :=
  atSt H ++ count2 H ++ [.addImm .x .x2 .x23 o, mov .x3 .x23]

theorem zext_check :
    ∃ hc, (Taint.check taint (Taint.ofRegs []) (.block [.addImm .w .x2 .x2 0]) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem skip_check : ∃ hc, (Taint.check taint (Taint.ofRegs []) (.block []) hc).isSome = true :=
  ⟨_, by taint_decide⟩

/-- The taint checks of the pieces of `iterate` between its calls. -/
structure Checks (H : Hash) : Prop where
  pro : ∃ hc, (Taint.check taint (Taint.ofRegs args) (.block (prologue H)) hc).isSome = true
  copyU : ∃ hc, (Taint.check taint (Taint.ofRegs (.x1 :: pubRegs)) (copy .x1 0 .x23 (uO H) H.D) hc).isSome = true
  copyK : ∀ o ∈ [0, H.S], ∃ hc,
    (Taint.check taint (Taint.ofRegs pubRegs) (copy .x19 o .x23 (stO H) H.S) hc).isSome = true
  upd : ∀ o ∈ [uO H, tmpO H], ∃ hc,
    (Taint.check taint (Taint.ofRegs pubRegs) (.block (updBlock H o)) hc).isSome = true
  fin : ∀ o ∈ [uO H, tmpO H], ∃ hc,
    (Taint.check taint (Taint.ofRegs pubRegs) (.block (finBlock H o)) hc).isSome = true
  xor : ∃ hc, (Taint.check taint (Taint.ofRegs pubRegs) (xorLoop H) hc).isSome = true
  dec : ∃ hc, (Taint.check taint (Taint.ofRegs pubRegs) (.block [.subImm .x .x22 .x22 1]) hc).isSome = true
  restore : ∃ hc, (Taint.check taint (Taint.ofRegs pubRegs) (.block H.restore) hc).isSome = true

/-- The public arguments are the same (`n` in its 32 bits). -/
structure PubEq (s₀ s₀' : State) : Prop where
  x0 : s₀.gpr .x0 = s₀'.gpr .x0
  x1 : s₀.gpr .x1 = s₀'.gpr .x1
  x2 : (s₀.gpr .x2).setWidth 32 = (s₀'.gpr .x2).setWidth 32
  x3 : s₀.gpr .x3 = s₀'.gpr .x3
  x4 : s₀.gpr .x4 = s₀'.gpr .x4
  sp : s₀.sp = s₀'.sp

variable {H : Hash} (hH : HashOK H) {sc : Nat}
variable {s₀ s₀' : State} (hp : Pre (H := H) sc s₀) (hp' : Pre (H := H) sc s₀') (hq : PubEq s₀ s₀')

theorem PubEq.nn (hq : PubEq s₀ s₀') : Generic.AArch64.nn s₀ = Generic.AArch64.nn s₀' := by
  show ((s₀.gpr .x2).setWidth 32).toNat = ((s₀'.gpr .x2).setWidth 32).toNat; rw [hq.x2]

theorem kr_agree (hq : PubEq s₀ s₀') {m : Nat} {s s' : State} (h : KR (H := H) sc s₀ m s)
    (h' : KR (H := H) sc s₀' m s') : s.sp = s'.sp ∧ ∀ r ∈ pubRegs, s.gpr r = s'.gpr r := by
  refine ⟨by rw [h.sp, h'.sp, hq.sp], fun r hr => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [h.x19, h'.x19, key, key, hq.x0]
  · rw [h.x20, h'.x20, tp, tp, hq.x3]
  · rw [h.x22, h'.x22]
  · rw [h.x23, h'.x23, scr, scr, hq.x4]

theorem eqs (hq : PubEq s₀ s₀') :
    ST (H := H) s₀' = ST (H := H) s₀ ∧ scr s₀' = scr s₀ ∧
      ∀ o : Nat, scr s₀' + BitVec.ofNat 64 o = scr s₀ + BitVec.ofNat 64 o :=
  ⟨by show s₀'.gpr .x4 + _ = s₀.gpr .x4 + _; rw [hq.x4], hq.x4.symm, fun o => by rw [scr, scr, hq.x4]⟩

include hH hp hp' hq

omit hH in
/-- A piece of code between calls that keeps `KR`. -/
theorem kr_rel {m : Nat} {c : Prog isa}
    (hck : ∃ hc, (Taint.check taint (Taint.ofRegs pubRegs) c hc).isSome = true)
    (hw : ∀ {t₀ : State}, Pre (H := H) sc t₀ → ∀ s, KR (H := H) sc t₀ m s → WP isa c s (KR (H := H) sc t₀ m)) :
    RelCT isa (fun s s' => KR (H := H) sc s₀ m s ∧ KR (H := H) sc s₀' m s') c
      fun s s' => KR (H := H) sc s₀ m s ∧ KR (H := H) sc s₀' m s' :=
  rel_taint pubRegs (fun _ _ h h' => kr_agree hq h h') hck (hw hp) (hw hp')

theorem upd_rel' {m : Nat} {o : Nat} (ho : o = uO H ∨ o = tmpO H) (hc : Checks H) :
    RelCT isa (fun s s' => KR (H := H) sc s₀ m s ∧ KR (H := H) sc s₀' m s')
      (H.callUpd (atSt H) H.B o H.D)
      fun s s' => KR (H := H) sc s₀ m s ∧ KR (H := H) sc s₀' m s' := by
  obtain ⟨e1, e2, e3⟩ := eqs hq (H := H)
  have ha := rel_taint (G := fun t => KR (H := H) sc s₀ m t ∧
      UpdArgs hH t (ST (H := H) s₀) (scr s₀ + BitVec.ofNat 64 o) (scr s₀) H.D ∧ t.gpr .x1 = BitVec.ofNat 64 H.B)
    (G' := fun t => KR (H := H) sc s₀' m t ∧
      UpdArgs hH t (ST (H := H) s₀) (scr s₀ + BitVec.ofNat 64 o) (scr s₀) H.D ∧ t.gpr .x1 = BitVec.ofNat 64 H.B)
    pubRegs (fun _ _ h h' => kr_agree hq h h') (hc.upd o (by rcases ho with rfl | rfl <;> simp))
    (fun s h => WP.mono (updArgs_ok hH hp h ho) fun _ ⟨k, a, x1, _⟩ => ⟨k, a, x1⟩)
    (fun s h => WP.mono (updArgs_ok hH hp' h ho) fun _ ⟨k, a, x1, _⟩ => ⟨k, e1 ▸ e3 o ▸ e2 ▸ a, x1⟩)
  exact ha.seq (rel_wp (upd_rel hH (st := ST (H := H) s₀) (d := scr s₀ + BitVec.ofNat 64 o) (sc := scr s₀)
    (len := H.D) fun s s' ⟨⟨k, a, x1⟩, ⟨k', a', x1'⟩⟩ => ⟨a, a', by rw [x1, x1'], by rw [k.sp, k'.sp, hq.sp]⟩)
    (fun _ ⟨k, a, _⟩ => updCall_ok hH hp k a fun _ k' _ _ => k')
    (fun _ ⟨k, a, _⟩ => updCall_ok hH hp' k (e1.symm ▸ e3 o ▸ e2.symm ▸ a) fun _ k' _ _ => k'))

theorem fin_rel' {m : Nat} {o : Nat} (ho : o = uO H ∨ o = tmpO H) (hc : Checks H) :
    RelCT isa (fun s s' => KR (H := H) sc s₀ m s ∧ KR (H := H) sc s₀' m s')
      (H.callFin (atSt H) (count2 H) o)
      fun s s' => KR (H := H) sc s₀ m s ∧ KR (H := H) sc s₀' m s' := by
  obtain ⟨e1, e2, e3⟩ := eqs hq (H := H)
  have ha := rel_taint (G := fun t => KR (H := H) sc s₀ m t ∧
      FinArgs hH t (ST (H := H) s₀) (scr s₀ + BitVec.ofNat 64 o) (scr s₀) ∧
      t.gpr .x1 = BitVec.ofNat 64 (H.B + H.D))
    (G' := fun t => KR (H := H) sc s₀' m t ∧
      FinArgs hH t (ST (H := H) s₀) (scr s₀ + BitVec.ofNat 64 o) (scr s₀) ∧
      t.gpr .x1 = BitVec.ofNat 64 (H.B + H.D))
    pubRegs (fun _ _ h h' => kr_agree hq h h') (hc.fin o (by rcases ho with rfl | rfl <;> simp))
    (fun s h => WP.mono (finArgs_ok hH hp h ho) fun _ ⟨k, a, x1, _⟩ => ⟨k, a, x1⟩)
    (fun s h => WP.mono (finArgs_ok hH hp' h ho) fun _ ⟨k, a, x1, _⟩ => ⟨k, e1 ▸ e3 o ▸ e2 ▸ a, x1⟩)
  exact ha.seq (rel_wp (fin_rel hH (st := ST (H := H) s₀) (o := scr s₀ + BitVec.ofNat 64 o) (sc := scr s₀)
    fun s s' ⟨⟨k, a, x1⟩, ⟨k', a', x1'⟩⟩ => ⟨a, a', by rw [x1, x1'], by rw [k.sp, k'.sp, hq.sp]⟩)
    (fun _ ⟨k, a, _⟩ => finCall_ok hH hp k ho a fun _ k' _ _ => k')
    (fun _ ⟨k, a, _⟩ => finCall_ok hH hp' k ho (e1.symm ▸ e3 o ▸ e2.symm ▸ a) fun _ k' _ _ => k'))

theorem body_rel (hc : Checks H) {m : Nat} (hm : 1 ≤ m) (hn : m < 2 ^ 64) :
    RelCT isa (fun s s' => KR (H := H) sc s₀ m s ∧ KR (H := H) sc s₀' m s') (body H)
      fun s s' => KR (H := H) sc s₀ (m - 1) s ∧ KR (H := H) sc s₀' (m - 1) s' := by
  have ck : ∀ {o : Nat}, (o = 0 ∨ o = H.S) → RelCT isa (fun s s' => KR (H := H) sc s₀ m s ∧ KR (H := H) sc s₀' m s')
      (copy .x19 o .x23 (stO H) H.S) fun s s' => KR (H := H) sc s₀ m s ∧ KR (H := H) sc s₀' m s' :=
    fun ho => kr_rel hp hp' hq (m := m) (hc.copyK _ (by rcases ho with rfl | rfl <;> simp))
      fun hp s k => WP.mono (copyKey_ok hH hp k ho) fun _ h => h.1
  have x := kr_rel hp hp' hq (m := m) hc.xor fun hp s k => WP.mono (xor'_ok hp k) fun _ h => h.1
  have d := rel_taint (G := KR (H := H) sc s₀ (m - 1)) (G' := KR (H := H) sc s₀' (m - 1)) pubRegs
    (fun _ _ h h' => kr_agree hq h h') hc.dec
    (fun s k => WP.mono (dec_ok hm hn k) fun _ h => h.1) (fun s k => WP.mono (dec_ok hm hn k) fun _ h => h.1)
  exact (ck (.inl rfl)).seq ((upd_rel' hH hp hp' hq (.inl rfl) hc).seq ((fin_rel' hH hp hp' hq (.inr rfl) hc).seq
    ((ck (.inr rfl)).seq ((upd_rel' hH hp hp' hq (.inr rfl) hc).seq ((fin_rel' hH hp hp' hq (.inl rfl) hc).seq
    (x.seq d))))))

/-- The loop's invariant in two runs, with `n` steps left. -/
abbrev LoopInv (n : Nat) (s s' : State) : Prop :=
  1 ≤ n ∧ n ≤ nn s₀ ∧ Inv hH sc s₀ n s ∧ Inv hH sc s₀' n s'

theorem step_rel (hc : Checks H) (n : Nat) :
    RelCT isa (LoopInv hH (sc := sc) (s₀ := s₀) (s₀' := s₀') n) (body H) fun s s' =>
      isa.eval (.nonzero .x .x22) s = isa.eval (.nonzero .x .x22) s' ∧
      (isa.eval (.nonzero .x .x22) s = some false → Inv hH sc s₀ 0 s ∧ Inv hH sc s₀' 0 s') ∧
      (isa.eval (.nonzero .x .x22) s = some true →
        ∃ m < n, LoopInv hH (sc := sc) (s₀ := s₀) (s₀' := s₀') m s s') := by
  have hlt := nn_lt (s₀ := s₀)
  by_cases hn : 1 ≤ n ∧ n ≤ nn s₀
  · have b := (body_rel hH hp hp' hq hc hn.1 (by omega)).mono (P' := LoopInv hH (sc := sc) (s₀ := s₀) (s₀' := s₀') n)
      (fun _ _ (h : LoopInv hH (sc := sc) (s₀ := s₀) (s₀' := s₀') n _ _) => ⟨h.2.2.1.kr, h.2.2.2.kr⟩)
      fun _ _ h => h
    refine (b.wp (F₁ := Inv hH sc s₀ (n - 1)) (F₂ := Inv hH sc s₀' (n - 1))
      fun s s' (h : LoopInv hH (sc := sc) (s₀ := s₀) (s₀' := s₀') n _ _) =>
        ⟨body_ok hH hp hn.1 (by omega) h.2.2.1, body_ok hH hp' hn.1 (by omega) h.2.2.2⟩).mono
      (fun _ _ h => h) fun t t' h => ?_
    obtain ⟨_, i, i'⟩ := h
    rw [nonzero_eval i.kr (by omega), nonzero_eval i'.kr (by omega)]
    refine ⟨rfl, fun hf => ?_, fun ht => ?_⟩
    · have hl : n - 1 = 0 := by simpa using hf
      exact ⟨hl ▸ i, hl ▸ i'⟩
    · have hl : n - 1 ≠ 0 := by simpa using ht
      exact ⟨n - 1, by omega, by omega, by omega, i, i'⟩
  · intro _ _ _ _ _ _ h
    exact absurd ⟨h.1, h.2.1⟩ hn

theorem loop_rel (hc : Checks H) :
    RelCT isa (fun s s' => Inv hH sc s₀ (nn s₀) s ∧ Inv hH sc s₀' (nn s₀') s')
      (.ite (.zero .x .x22) (.block []) (.loop (body H) (.nonzero .x .x22)))
      fun s s' => Inv hH sc s₀ 0 s ∧ Inv hH sc s₀' 0 s' := by
  have hN := hq.nn
  have hlt := nn_lt (s₀ := s₀)
  have hlt' := nn_lt (s₀ := s₀')
  refine RelCT.ite (fun s s' h => by rw [zero_eval h.1.kr (by omega), zero_eval h.2.kr (by omega), hN]) ?_ ?_
  · by_cases e : nn s₀ = 0
    · have e' : nn s₀' = 0 := hN ▸ e
      exact (rel_taint (c := .block []) (F := Inv hH sc s₀ (nn s₀)) (F' := Inv hH sc s₀' (nn s₀'))
        (G := Inv hH sc s₀ 0) (G' := Inv hH sc s₀' 0) []
        (fun s s' h h' => ⟨by rw [h.kr.sp, h'.kr.sp, hq.sp], by simp⟩) skip_check
        (fun s h => WP.block_nil (e ▸ h)) (fun s h => WP.block_nil (e' ▸ h))).mono (fun _ _ h => h.1)
        fun _ _ h => h
    · intro _ _ _ _ _ _ h
      have z := h.2
      rw [zero_eval h.1.1.kr (by omega)] at z
      exact absurd (by simpa using z) e
  · refine (RelCT.loop (M := isa) (LoopInv hH (sc := sc) (s₀ := s₀) (s₀' := s₀')) (step_rel hH hp hp' hq hc)
      (nn s₀)).mono (fun s s' h => ?_) fun _ _ h => h
    have z := h.2
    rw [zero_eval h.1.1.kr (by omega)] at z
    have e : nn s₀ ≠ 0 := by simpa using z
    exact ⟨by omega, (Nat.le_refl _), h.1.1, hN ▸ h.1.2⟩

theorem ct (hc : Checks H) : RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') (iterate H) fun _ _ => True := by
  have hN := hq.nn
  have zx := rel_taint (F := fun s => s = s₀) (F' := fun s => s = s₀')
    (G := fun s => Upd s₀ s .x2 (BitVec.ofNat 64 (nn s₀))) (G' := fun s => Upd s₀' s .x2 (BitVec.ofNat 64 (nn s₀')))
    [] (fun s s' e e' => ⟨by rw [e, e', hq.sp], by simp⟩) zext_check
    (fun _ e => by rw [e]; exact zext_ok) (fun _ e => by rw [e]; exact zext_ok)
  have pro := rel_taint (F := fun s => Upd s₀ s .x2 (BitVec.ofNat 64 (nn s₀)))
    (F' := fun s => Upd s₀' s .x2 (BitVec.ofNat 64 (nn s₀')))
    (G := fun s => KR (H := H) sc s₀ (nn s₀) s ∧ s.gpr .x1 = up s₀ ∧ Frame [saveR H (scr s₀)] s₀.mem s.mem)
    (G' := fun s => KR (H := H) sc s₀' (nn s₀') s ∧ s.gpr .x1 = up s₀' ∧ Frame [saveR H (scr s₀')] s₀'.mem s.mem)
    args (fun s s' u u' => ⟨by rw [u.sp, u'.sp, hq.sp], fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl
        · rw [u.other _ (by decide), u'.other _ (by decide), hq.x0]
        · rw [u.other _ (by decide), u'.other _ (by decide), hq.x1]
        · rw [u.gpr, u'.gpr, hN]
        · rw [u.other _ (by decide), u'.other _ (by decide), hq.x3]
        · rw [u.other _ (by decide), u'.other _ (by decide), hq.x4]⟩) hc.pro
    (fun _ u => pro_ok hp u) (fun _ u => pro_ok hp' u)
  have cu := rel_taint
    (F := fun s => KR (H := H) sc s₀ (nn s₀) s ∧ s.gpr .x1 = up s₀ ∧ Frame [saveR H (scr s₀)] s₀.mem s.mem)
    (F' := fun s => KR (H := H) sc s₀' (nn s₀') s ∧ s.gpr .x1 = up s₀' ∧ Frame [saveR H (scr s₀')] s₀'.mem s.mem)
    (G := Inv hH sc s₀ (nn s₀)) (G' := Inv hH sc s₀' (nn s₀')) (.x1 :: pubRegs)
    (fun s s' h h' => by
      obtain ⟨sp, hr⟩ := kr_agree hq h.1 (hN ▸ h'.1)
      refine ⟨sp, fun r hm => ?_⟩
      rcases List.mem_cons.mp hm with rfl | hm
      · rw [h.2.1, h'.2.1, up, up, hq.x1]
      · exact hr r hm) hc.copyU
    (fun s h => copyU_ok hH hp h.1 h.2.1 h.2.2) (fun s h => copyU_ok hH hp' h.1 h.2.1 h.2.2)
  obtain ⟨_, hr⟩ := hc.restore
  have restore : RelCT isa (fun s s' => Inv hH sc s₀ 0 s ∧ Inv hH sc s₀' 0 s') (.block H.restore)
      fun _ _ => True :=
    RelCT.taint (A := taint) (Taint.ofRegs pubRegs) (fun _ _ h => by
      obtain ⟨sp, hr⟩ := kr_agree hq h.1.kr h.2.kr
      exact ⟨sp, fun r hm => hr r (Taint.mem_ofRegs.mp hm)⟩) hr
  exact zx.seq (pro.seq (cu.seq ((loop_rel hH hp hp' hq hc).seq restore)))

end VG.Proof.Pbkdf2.Generic.AArch64

namespace VG.Proof.Pbkdf2.Generic.AArch64

open VG.AArch64
open VG.Impl.Hmac.Generic.AArch64 (Hash)
open VG.Proof.Hmac.Generic.AArch64

/-- `iterate` is verified against `iterG`, given the taint checks, which the
kernel evaluates for each hash function. -/
theorem verified {H : Hash} (hH : HashOK H) {sc : Nat} (hc : Checks H)
    (hfit : H.buf + H.S + 2 * H.F ≤ 8 * sc) (hsat : ∃ s, (iterG hH.SH sc).pre s) :
    Verified AArch64.target (VG.Impl.Pbkdf2.Generic.AArch64.iterate H) (iterG hH.SH sc) := by
  refine ⟨fun s hs => correct hH (pre_of hH sc hs hfit), fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, hsat⟩
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hpub
  exact (ct hH (pre_of hH sc h₁ hfit) (pre_of hH sc h₂ hfit) ⟨h1, h2, h3, h4, h5, h6⟩ hc
    _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.Pbkdf2.Generic.AArch64
