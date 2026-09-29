import VerifiedGarbage.Proof.Pbkdf2.Generic.X86_64.Iterate

/-!
# PBKDF2-HMAC over any streaming hash function on x86-64: `iterate`, constant time

Untrusted: everything here is checked by Lean. As for HMAC's `init`
(`Proof/Hmac/Generic/X86_64/InitCT.lean`), with a loop: its count is `n`,
public, and the two runs run the same number of steps (`RelCT.loop`).
-/

namespace VG

/-- A branch, in two runs whose condition agrees. -/
theorem RelCT.ite {M : ISA} {P Q : M.State → M.State → Prop} {c : M.Cond} {th el : Prog M}
    (hc : ∀ s s', P s s' → M.eval c s = M.eval c s')
    (ht : RelCT M (fun s s' => P s s' ∧ M.eval c s = some true) th Q)
    (he : RelCT M (fun s s' => P s s' ∧ M.eval c s = some false) el Q) :
    RelCT M P (.ite c th el) Q := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  have h := hc _ _ hp
  cases e₁ with
  | iteT c₁ b₁ =>
    cases e₂ with
    | iteT _ b₂ => obtain ⟨rfl, hq⟩ := ht _ _ _ _ _ _ ⟨hp, c₁⟩ b₁ b₂; exact ⟨rfl, hq⟩
    | iteF c₂ _ => rw [c₁, c₂] at h; cases h
  | iteF c₁ b₁ =>
    cases e₂ with
    | iteT c₂ _ => rw [c₁, c₂] at h; cases h
    | iteF _ b₂ => obtain ⟨rfl, hq⟩ := he _ _ _ _ _ _ ⟨hp, c₁⟩ b₁ b₂; exact ⟨rfl, hq⟩

end VG

namespace VG.Proof.Pbkdf2.Generic.X86_64

open VG.X86_64
open VG.Impl.Hmac.Generic.X86_64 (Hash copy)
open VG.Impl.Pbkdf2.Generic.X86_64 (stO tmpO uO xorLoop count2 body prologue iterate)
open VG.Proof.Hmac.Generic.X86_64

/-- The arguments that are public in all their bits. -/
abbrev args : List Reg := [.rdi, .rsi, .rcx, .r8, .rsp]

/-- The block that sets up a call of `update` on the state, with `D` bytes at `scratch + o`. -/
abbrev updBlock (H : Hash) (o : Nat) : List Instr :=
  VG.Impl.Hmac.Generic.X86_64.scr .rdi (stO H) ++ [.mov32 .rsi (.imm (BitVec.ofNat 32 H.B))] ++
    VG.Impl.Hmac.Generic.X86_64.scr .rdx o ++ [.mov32 .rcx (.imm (BitVec.ofNat 32 H.D)), .mov .r8 (.reg .r15)]

/-- The block that sets up a call of `finalize` on the state, into `scratch + o`. -/
abbrev finBlock (H : Hash) (o : Nat) : List Instr :=
  VG.Impl.Hmac.Generic.X86_64.scr .rdi (stO H) ++ count2 H ++ VG.Impl.Hmac.Generic.X86_64.scr .rdx o ++
    [.mov .rcx (.reg .r15)]

/-- The taint checks of the pieces of `iterate` between its calls. -/
structure Checks (H : Hash) : Prop where
  pro : ∃ hc, (Taint.check taint (Taint.ofRegs args) (.block (prologue H)) hc).isSome = true
  copyU : ∃ hc, (Taint.check taint (Taint.ofRegs (.rsi :: kregs)) (copy .rsi 0 .r15 (uO H) H.D) hc).isSome = true
  test : ∃ hc, (Taint.check taint (Taint.ofRegs kregs) (.block [.alu .test .r13 (.reg .r13)]) hc).isSome = true
  copyK : ∀ o ∈ [0, H.S], ∃ hc,
    (Taint.check taint (Taint.ofRegs kregs) (copy .rbx o .r15 (stO H) H.S) hc).isSome = true
  upd : ∀ o ∈ [uO H, tmpO H], ∃ hc,
    (Taint.check taint (Taint.ofRegs kregs) (.block (updBlock H o)) hc).isSome = true
  fin : ∀ o ∈ [uO H, tmpO H], ∃ hc,
    (Taint.check taint (Taint.ofRegs kregs) (.block (finBlock H o)) hc).isSome = true
  xor : ∃ hc, (Taint.check taint (Taint.ofRegs kregs) (xorLoop H) hc).isSome = true
  dec : ∃ hc, (Taint.check taint (Taint.ofRegs kregs) (.block [.alu .sub .r13 (.imm 1)]) hc).isSome = true
  restore : ∃ hc, (Taint.check taint (Taint.ofRegs kregs) (.block H.restore) hc).isSome = true

/-- The public arguments are the same (`n` in its 32 bits). -/
structure PubEq (s₀ s₀' : State) : Prop where
  rdi : s₀.gpr .rdi = s₀'.gpr .rdi
  rsi : s₀.gpr .rsi = s₀'.gpr .rsi
  rdx : (s₀.gpr .rdx).setWidth 32 = (s₀'.gpr .rdx).setWidth 32
  rcx : s₀.gpr .rcx = s₀'.gpr .rcx
  r8 : s₀.gpr .r8 = s₀'.gpr .r8
  rsp : s₀.gpr .rsp = s₀'.gpr .rsp

variable {H : Hash} (hH : HashOK H) {sc : Nat}
variable {s₀ s₀' : State} (hp : Pre (H := H) sc s₀) (hp' : Pre (H := H) sc s₀') (hq : PubEq s₀ s₀')

theorem PubEq.nn (hq : PubEq s₀ s₀') : Generic.X86_64.nn s₀ = Generic.X86_64.nn s₀' := by
  show ((s₀.gpr .rdx).setWidth 32).toNat = ((s₀'.gpr .rdx).setWidth 32).toNat; rw [hq.rdx]

theorem kr_agree (hq : PubEq s₀ s₀') {m : Nat} {s s' : State} (h : KR (H := H) sc s₀ m s)
    (h' : KR (H := H) sc s₀' m s') : ∀ r ∈ kregs, s.gpr r = s'.gpr r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · rw [h.rbx, h'.rbx, key, key, hq.rdi]
  · rw [h.r12, h'.r12, tp, tp, hq.rcx]
  · rw [h.r13, h'.r13]
  · rw [h.r15, h'.r15, scr, scr, hq.r8]
  · rw [h.rsp, h'.rsp, hq.rsp]

theorem eqs (hq : PubEq s₀ s₀') :
    ST (H := H) s₀' = ST (H := H) s₀ ∧ scr s₀' = scr s₀ ∧ ∀ o : Nat, scr s₀' + BitVec.ofNat 64 o = scr s₀ + BitVec.ofNat 64 o :=
  ⟨by show s₀'.gpr .r8 + _ = s₀.gpr .r8 + _; rw [hq.r8], hq.r8.symm, fun o => by rw [scr, scr, hq.r8]⟩

include hH hp hp' hq

omit hH in
/-- A piece of code between calls that keeps `KR`. -/
theorem kr_rel {m : Nat} {c : Prog isa}
    (hck : ∃ hc, (Taint.check taint (Taint.ofRegs kregs) c hc).isSome = true)
    (hw : ∀ {t₀ : State}, Pre (H := H) sc t₀ → ∀ s, KR (H := H) sc t₀ m s → WP isa c s (KR (H := H) sc t₀ m)) :
    RelCT isa (fun s s' => KR (H := H) sc s₀ m s ∧ KR (H := H) sc s₀' m s') c
      fun s s' => KR (H := H) sc s₀ m s ∧ KR (H := H) sc s₀' m s' :=
  rel_taint kregs (fun _ _ h h' => kr_agree hq h h') hck (hw hp) (hw hp')

theorem upd_rel' {m : Nat} {o : Nat} (ho : o = uO H ∨ o = tmpO H) (hc : Checks H) :
    RelCT isa (fun s s' => KR (H := H) sc s₀ m s ∧ KR (H := H) sc s₀' m s')
      (H.callUpd (VG.Impl.Hmac.Generic.X86_64.scr .rdi (stO H)) H.B o H.D)
      fun s s' => KR (H := H) sc s₀ m s ∧ KR (H := H) sc s₀' m s' := by
  obtain ⟨e1, e2, e3⟩ := eqs hq (H := H)
  have ha := rel_taint (G := fun t => KR (H := H) sc s₀ m t ∧
      UpdArgs hH t (ST (H := H) s₀) (scr s₀ + BitVec.ofNat 64 o) (scr s₀) H.D ∧ t.gpr .rsi = BitVec.ofNat 64 H.B)
    (G' := fun t => KR (H := H) sc s₀' m t ∧
      UpdArgs hH t (ST (H := H) s₀) (scr s₀ + BitVec.ofNat 64 o) (scr s₀) H.D ∧ t.gpr .rsi = BitVec.ofNat 64 H.B)
    kregs (fun _ _ h h' => kr_agree hq h h') (hc.upd o (by rcases ho with rfl | rfl <;> simp))
    (fun s h => WP.mono (updArgs_ok hH hp h ho) fun _ ⟨k, a, si, _⟩ => ⟨k, a, si⟩)
    (fun s h => WP.mono (updArgs_ok hH hp' h ho) fun _ ⟨k, a, si, _⟩ => ⟨k, e1 ▸ e3 o ▸ e2 ▸ a, si⟩)
  exact ha.seq (rel_wp (upd_rel hH (st := ST (H := H) s₀) (d := scr s₀ + BitVec.ofNat 64 o) (sc := scr s₀)
    (len := H.D) fun s s' ⟨⟨k, a, si⟩, ⟨k', a', si'⟩⟩ => ⟨a, a', by rw [si, si'], by rw [k.rsp, k'.rsp, hq.rsp]⟩)
    (fun _ ⟨k, a, _⟩ => updCall_ok hH hp k a fun _ k' _ _ => k')
    (fun _ ⟨k, a, _⟩ => updCall_ok hH hp' k (e1.symm ▸ e3 o ▸ e2.symm ▸ a) fun _ k' _ _ => k'))

theorem fin_rel' {m : Nat} {o : Nat} (ho : o = uO H ∨ o = tmpO H) (hc : Checks H) :
    RelCT isa (fun s s' => KR (H := H) sc s₀ m s ∧ KR (H := H) sc s₀' m s')
      (H.callFin (VG.Impl.Hmac.Generic.X86_64.scr .rdi (stO H)) (count2 H) o)
      fun s s' => KR (H := H) sc s₀ m s ∧ KR (H := H) sc s₀' m s' := by
  obtain ⟨e1, e2, e3⟩ := eqs hq (H := H)
  have ha := rel_taint (G := fun t => KR (H := H) sc s₀ m t ∧
      FinArgs hH t (ST (H := H) s₀) (scr s₀ + BitVec.ofNat 64 o) (scr s₀) ∧
      t.gpr .rsi = BitVec.ofNat 64 (H.B + H.D))
    (G' := fun t => KR (H := H) sc s₀' m t ∧
      FinArgs hH t (ST (H := H) s₀) (scr s₀ + BitVec.ofNat 64 o) (scr s₀) ∧
      t.gpr .rsi = BitVec.ofNat 64 (H.B + H.D))
    kregs (fun _ _ h h' => kr_agree hq h h') (hc.fin o (by rcases ho with rfl | rfl <;> simp))
    (fun s h => WP.mono (finArgs_ok hH hp h ho) fun _ ⟨k, a, si, _⟩ => ⟨k, a, si⟩)
    (fun s h => WP.mono (finArgs_ok hH hp' h ho) fun _ ⟨k, a, si, _⟩ => ⟨k, e1 ▸ e3 o ▸ e2 ▸ a, si⟩)
  exact ha.seq (rel_wp (fin_rel hH (st := ST (H := H) s₀) (o := scr s₀ + BitVec.ofNat 64 o) (sc := scr s₀)
    fun s s' ⟨⟨k, a, si⟩, ⟨k', a', si'⟩⟩ => ⟨a, a', by rw [si, si'], by rw [k.rsp, k'.rsp, hq.rsp]⟩)
    (fun _ ⟨k, a, _⟩ => finCall_ok hH hp k ho a fun _ k' _ _ => k')
    (fun _ ⟨k, a, _⟩ => finCall_ok hH hp' k ho (e1.symm ▸ e3 o ▸ e2.symm ▸ a) fun _ k' _ _ => k'))

theorem body_rel (hc : Checks H) {m : Nat} (hm : 1 ≤ m) (hn : m < 2 ^ 64) :
    RelCT isa (fun s s' => KR (H := H) sc s₀ m s ∧ KR (H := H) sc s₀' m s') (body H)
      fun s s' => (KR (H := H) sc s₀ (m - 1) s ∧ s.zf = some (decide (m - 1 = 0))) ∧
        (KR (H := H) sc s₀' (m - 1) s' ∧ s'.zf = some (decide (m - 1 = 0))) := by
  have ck : ∀ {o : Nat}, (o = 0 ∨ o = H.S) → RelCT isa (fun s s' => KR (H := H) sc s₀ m s ∧ KR (H := H) sc s₀' m s')
      (copy .rbx o .r15 (stO H) H.S) fun s s' => KR (H := H) sc s₀ m s ∧ KR (H := H) sc s₀' m s' :=
    fun ho => kr_rel hp hp' hq (m := m) (hc.copyK _ (by rcases ho with rfl | rfl <;> simp))
      fun hp s k => WP.mono (copyKey_ok hH hp k ho) fun _ h => h.1
  have x := kr_rel hp hp' hq (m := m) hc.xor fun hp s k => WP.mono (xor'_ok hp k) fun _ h => h.1
  have d : RelCT isa (fun s s' => KR (H := H) sc s₀ m s ∧ KR (H := H) sc s₀' m s')
      (.block [.alu .sub .r13 (.imm 1)])
      fun s s' => (KR (H := H) sc s₀ (m - 1) s ∧ s.zf = some (decide (m - 1 = 0))) ∧
        (KR (H := H) sc s₀' (m - 1) s' ∧ s'.zf = some (decide (m - 1 = 0))) :=
    rel_taint kregs (fun _ _ h h' => kr_agree hq h h') hc.dec
      (fun s k => WP.mono (dec_ok hm hn k) fun _ ⟨k, z, _⟩ => ⟨k, z⟩)
      (fun s k => WP.mono (dec_ok hm hn k) fun _ ⟨k, z, _⟩ => ⟨k, z⟩)
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
    refine (b.wp (F₁ := fun (t : State) => Inv hH sc s₀ (n - 1) t ∧ t.zf = some (decide (n - 1 = 0)))
      (F₂ := fun (t : State) => Inv hH sc s₀' (n - 1) t ∧ t.zf = some (decide (n - 1 = 0)))
      fun s s' (h : LoopInv hH (sc := sc) (s₀ := s₀) (s₀' := s₀') n _ _) =>
        ⟨body_ok hH hp hn.1 (by omega) h.2.2.1, body_ok hH hp' hn.1 (by omega) h.2.2.2⟩).mono
      (fun _ _ h => h) fun t t' h => ?_
    obtain ⟨_, ⟨i, z⟩, ⟨i', z'⟩⟩ := h
    have ev : ∀ x : State, isa.eval .ne x = x.zf.map (!·) := fun _ => rfl
    rw [ev, ev, z, z']
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
      (.ite .e (.block []) (.loop (body H) .ne)) fun s s' => Inv hH sc s₀ 0 s ∧ Inv hH sc s₀' 0 s' := by
  have hN := hq.nn
  refine RelCT.ite (fun s s' h => by simp [eval, h.1.2, h.2.2, hN]) ?_ ?_
  · refine ((RelCT.taint (A := taint) (Taint.ofRegs []) (fun _ _ _ => Taint.agree_ofRegs (by simp))
      (c := .block []) (by taint_decide)).wp (F₁ := Inv hH sc s₀ 0) (F₂ := Inv hH sc s₀' 0)
      fun s s' h => ?_).mono (fun _ _ h => h) fun _ _ h => h.2
    have e : nn s₀ = 0 := by simpa [eval, h.1.1.2] using h.2
    have e' : nn s₀' = 0 := hN ▸ e
    exact ⟨WP.block_nil (e ▸ h.1.1.1), WP.block_nil (e' ▸ h.1.2.1)⟩
  · refine (RelCT.loop (M := isa) (LoopInv hH (sc := sc) (s₀ := s₀) (s₀' := s₀')) (step_rel hH hp hp' hq hc)
      (nn s₀)).mono (fun s s' h => ?_) fun _ _ h => h
    have e : nn s₀ ≠ 0 := by simpa [eval, h.1.1.2] using h.2
    exact ⟨by omega, (Nat.le_refl _), h.1.1.1, hN ▸ h.1.2.1⟩

theorem ct (hc : Checks H) : RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') (iterate H) fun _ _ => True := by
  have hN := hq.nn
  have pro := rel_taint (F := fun s => s = s₀) (F' := fun s => s = s₀')
    (G := fun s => KR (H := H) sc s₀ (nn s₀) s ∧ s.gpr .rsi = up s₀ ∧ Frame [saveR H (scr s₀)] s₀.mem s.mem)
    (G' := fun s => KR (H := H) sc s₀' (nn s₀') s ∧ s.gpr .rsi = up s₀' ∧ Frame [saveR H (scr s₀')] s₀'.mem s.mem)
    args (fun s s' e e' r hr => by
        rw [e, e']
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl
        · exact hq.rdi
        · exact hq.rsi
        · exact hq.rcx
        · exact hq.r8
        · exact hq.rsp) hc.pro
    (fun _ e => by rw [e]; exact pro_ok hp) (fun _ e => by rw [e]; exact pro_ok hp')
  have cu := rel_taint
    (F := fun s => KR (H := H) sc s₀ (nn s₀) s ∧ s.gpr .rsi = up s₀ ∧ Frame [saveR H (scr s₀)] s₀.mem s.mem)
    (F' := fun s => KR (H := H) sc s₀' (nn s₀') s ∧ s.gpr .rsi = up s₀' ∧ Frame [saveR H (scr s₀')] s₀'.mem s.mem)
    (G := Inv hH sc s₀ (nn s₀)) (G' := Inv hH sc s₀' (nn s₀')) (.rsi :: kregs)
    (fun s s' h h' r hr => by
      rcases List.mem_cons.mp hr with rfl | hr
      · rw [h.2.1, h'.2.1, up, up, hq.rsi]
      · exact kr_agree hq h.1 (hN ▸ h'.1) r hr) hc.copyU
    (fun s h => copyU_ok hH hp h.1 h.2.1 h.2.2) (fun s h => copyU_ok hH hp' h.1 h.2.1 h.2.2)
  have te := rel_taint (F := Inv hH sc s₀ (nn s₀)) (F' := Inv hH sc s₀' (nn s₀'))
    (G := fun t => Inv hH sc s₀ (nn s₀) t ∧ t.zf = some (decide (nn s₀ = 0)))
    (G' := fun t => Inv hH sc s₀' (nn s₀') t ∧ t.zf = some (decide (nn s₀' = 0))) kregs
    (fun s s' h h' => kr_agree hq h.kr (hN ▸ h'.kr)) hc.test (fun s h => test_ok hH h) (fun s h => test_ok hH h)
  obtain ⟨_, hr⟩ := hc.restore
  have restore : RelCT isa (fun s s' => Inv hH sc s₀ 0 s ∧ Inv hH sc s₀' 0 s') (.block H.restore)
      fun _ _ => True :=
    RelCT.taint (A := taint) (Taint.ofRegs kregs) (fun _ _ h => Taint.agree_ofRegs (kr_agree hq h.1.kr h.2.kr)) hr
  exact pro.seq (cu.seq (te.seq ((loop_rel hH hp hp' hq hc).seq restore)))

end VG.Proof.Pbkdf2.Generic.X86_64

namespace VG.Proof.Pbkdf2.Generic.X86_64

open VG.X86_64
open VG.Impl.Hmac.Generic.X86_64 (Hash)
open VG.Proof.Hmac.Generic.X86_64

/-- `iterate` is verified against `iterG`, given the taint checks and the
facts about its code that the kernel checks for each hash function. -/
theorem verified {H : Hash} (hH : HashOK H) {sc : Nat} (hc : Checks H)
    (hfit : H.buf + H.S + 2 * H.F ≤ 8 * sc)
    (hmx : (VG.Impl.Pbkdf2.Generic.X86_64.iterate H).allInstrs (fun i => !loadsMxcsr i) = true)
    (hsat : ∃ s, (iterG hH.SH sc).pre s) :
    Verified X86_64.target (VG.Impl.Pbkdf2.Generic.X86_64.iterate H) (iterG hH.SH sc) := by
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, hsat⟩
  · obtain ⟨t, s', he, hg, hpost⟩ := correct hH (pre_of hH sc hs hfit)
    exact ⟨t, s', he, abiPreserved_of_exec hmx he hg, hpost⟩
  · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hpub
    exact (ct hH (pre_of hH sc h₁ hfit) (pre_of hH sc h₂ hfit) ⟨h1, h2, h3, h4, h5, h6⟩ hc
      _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.Pbkdf2.Generic.X86_64
