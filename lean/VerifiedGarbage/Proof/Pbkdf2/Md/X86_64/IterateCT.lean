import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Iterate

/-!
# PBKDF2-HMAC over any Merkle–Damgård hash function on x86-64: `iterate`, constant time

Untrusted: everything here is checked by Lean. The pieces between the calls
of the compression function are checked by the taint analysis (`Checks`,
`by taint_decide` for each hash function), with the registers `KR` fixes
public: they are the same in two runs that agree on the public arguments.
The calls are constant time by the compression function's own proof
(`compressAt_rel`), and the loop runs `n` steps in both runs.
-/

namespace VG.Proof.Pbkdf2.Md.X86_64

open VG.X86_64 VG.Proof.MdStream VG.Proof.MdStream.X86_64
open VG.Impl.MdStream.X86_64 (restore compressAt)
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)
open VG.Proof.Hmac.Generic.X86_64 (iterG rel_taint rel_wp)

/-- The arguments that are public in all their bits. -/
abbrev args : List Reg := [.rdi, .rsi, .rcx, .r8, .rsp]

/-- The taint checks of the pieces of `iterate` between its calls. -/
structure Checks (H : Hash) : Prop where
  pro : ∃ hc, (Taint.check taint (Taint.ofRegs args) (.block H.iterPrologue) hc).isSome = true
  load : ∃ hc, (Taint.check taint (Taint.ofRegs kregs) (.block (H.load 0)) hc).isSome = true
  mid : ∃ hc, (Taint.check taint (Taint.ofRegs kregs) (.block (H.P.out ++ H.fix ++ H.load H.S)) hc).isSome
    = true
  last : ∃ hc, (Taint.check taint (Taint.ofRegs kregs)
    (.block (H.P.out ++ H.fix ++ H.xor32 ++ [.alu .sub .r13 (.imm 1)])) hc).isSome = true
  restore : ∃ hc, (Taint.check taint (Taint.ofRegs kregs) (.block (restore H.P)) hc).isSome = true

/-- The public arguments are the same (`n` in its 32 bits). -/
structure PubEq (s₀ s₀' : State) : Prop where
  rdi : s₀.gpr .rdi = s₀'.gpr .rdi
  rsi : s₀.gpr .rsi = s₀'.gpr .rsi
  rdx : (s₀.gpr .rdx).setWidth 32 = (s₀'.gpr .rdx).setWidth 32
  rcx : s₀.gpr .rcx = s₀'.gpr .rcx
  r8 : s₀.gpr .r8 = s₀'.gpr .r8
  rsp : s₀.gpr .rsp = s₀'.gpr .rsp

section
variable {H : Hash} (hH : HashOK H)
variable {s₀ s₀' : State} (hp : Pre (H := H) s₀) (hp' : Pre (H := H) s₀') (hz : Sizes H) (hq : PubEq s₀ s₀')

theorem PubEq.nn (hq : PubEq s₀ s₀') : X86_64.nn s₀ = X86_64.nn s₀' := by
  show ((s₀.gpr .rdx).setWidth 32).toNat = ((s₀'.gpr .rdx).setWidth 32).toNat; rw [hq.rdx]

theorem kr_agree (hq : PubEq s₀ s₀') {m : Nat} {s s' : State} (h : KR (H := H) s₀ m s)
    (h' : KR (H := H) s₀' m s') : ∀ r ∈ kregs, s.gpr r = s'.gpr r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [h.rbx, h'.rbx, ST, ST, scr, scr, hq.r8]
  · rw [h.rbp, h'.rbp, BL, BL, scr, scr, hq.r8]
  · rw [h.r12, h'.r12, key, key, hq.rdi]
  · rw [h.r13, h'.r13]
  · rw [h.r14, h'.r14, tp, tp, hq.rcx]
  · rw [h.r15, h'.r15, scr, scr, hq.r8]
  · rw [h.rsp, h'.rsp, hq.rsp]

include hH hp hp' hz hq

/-- A call of the compression function, with the block in `rsi`. -/
theorem cmp_rel {m : Nat} :
    RelCT isa (fun s s' => (KR (H := H) s₀ m s ∧ s.gpr .rsi = BL (H := H) s₀) ∧
        (KR (H := H) s₀' m s' ∧ s'.gpr .rsi = BL (H := H) s₀'))
      (compressAt H.compN H.compC) fun s s' => KR (H := H) s₀ m s ∧ KR (H := H) s₀' m s' :=
  rel_wp (compressAt_rel hH.md hH.comp fun s s' ⟨⟨k, si⟩, ⟨k', si'⟩⟩ =>
      ⟨⟨_, _, _, kr_call hp hz k si⟩, ⟨_, _, _, kr_call hp' hz k' si'⟩, kr_agree hq k k' _ (by simp),
        kr_agree hq k k' _ (by simp), by rw [si, si', BL, BL, scr, scr, hq.r8], kr_agree hq k k' _ (by simp)⟩)
    (fun _ ⟨k, si⟩ => WP.mono (cmp_ok hH hp hz k si) fun _ h => h.1)
    (fun _ ⟨k, si⟩ => WP.mono (cmp_ok hH hp' hz k si) fun _ h => h.1)

theorem body_rel (hc : Checks H) {m : Nat} (hm : 1 ≤ m) (hn : m < 2 ^ 64) :
    RelCT isa (fun s s' => KR (H := H) s₀ m s ∧ KR (H := H) s₀' m s') H.body
      fun s s' => (KR (H := H) s₀ (m - 1) s ∧ s.zf = some (decide (m - 1 = 0))) ∧
        (KR (H := H) s₀' (m - 1) s' ∧ s'.zf = some (decide (m - 1 = 0))) := by
  have ag := fun (s s' : State) (h : KR (H := H) s₀ m s) (h' : KR (H := H) s₀' m s') => kr_agree hq h h'
  have l₁ := rel_taint (G := fun t => KR (H := H) s₀ m t ∧ t.gpr .rsi = BL (H := H) s₀)
    (G' := fun t => KR (H := H) s₀' m t ∧ t.gpr .rsi = BL (H := H) s₀') kregs ag hc.load
    (fun s k => by
      rw [← List.append_nil (H.load 0)]
      exact load_ok hH hp hz k (o := 0) (by have := hz.N; have : H.S = H.P.N + H.P.B := rfl; omega) fun _ k' si _ _ => WP.block_nil ⟨k', si⟩)
    (fun s k => by
      rw [← List.append_nil (H.load 0)]
      exact load_ok hH hp' hz k (o := 0) (by have := hz.N; have : H.S = H.P.N + H.P.B := rfl; omega) fun _ k' si _ _ => WP.block_nil ⟨k', si⟩)
  have l₂ := rel_taint (G := fun t => KR (H := H) s₀ m t ∧ t.gpr .rsi = BL (H := H) s₀)
    (G' := fun t => KR (H := H) s₀' m t ∧ t.gpr .rsi = BL (H := H) s₀') kregs ag hc.mid
    (fun s k => outFix_ok hH hp hz k fun _ k₁ _ _ => by
      rw [← List.append_nil (H.load H.S)]
      exact load_ok hH hp hz k₁ (o := H.S) (by have := hz.N; have : H.S = H.P.N + H.P.B := rfl; omega)
        fun _ k' si _ _ => WP.block_nil ⟨k', si⟩)
    (fun s k => outFix_ok hH hp' hz k fun _ k₁ _ _ => by
      rw [← List.append_nil (H.load H.S)]
      exact load_ok hH hp' hz k₁ (o := H.S) (by have := hz.N; have : H.S = H.P.N + H.P.B := rfl; omega)
        fun _ k' si _ _ => WP.block_nil ⟨k', si⟩)
  have l₃ := rel_taint (G := fun t => KR (H := H) s₀ (m - 1) t ∧ t.zf = some (decide (m - 1 = 0)))
    (G' := fun t => KR (H := H) s₀' (m - 1) t ∧ t.zf = some (decide (m - 1 = 0))) kregs ag hc.last
    (fun s k => by
      rw [List.append_assoc (H.P.out ++ H.fix)]
      exact outFix_ok hH hp hz k fun _ k₁ _ _ => WP.mono (xorDec_ok hp hz hm hn k₁) fun _ h => ⟨h.1, h.2.1⟩)
    (fun s k => by
      rw [List.append_assoc (H.P.out ++ H.fix)]
      exact outFix_ok hH hp' hz k fun _ k₁ _ _ => WP.mono (xorDec_ok hp' hz hm hn k₁) fun _ h => ⟨h.1, h.2.1⟩)
  have c := cmp_rel hH hp hp' hz hq (m := m)
  exact l₁.seq (c.seq (l₂.seq (c.seq l₃)))

/-- The loop's invariant in two runs, with `n` steps left. -/
abbrev LoopInv (n : Nat) (s s' : State) : Prop :=
  1 ≤ n ∧ n ≤ nn s₀ ∧ Inv hH s₀ n s ∧ Inv hH s₀' n s'

theorem step_rel (hc : Checks H) (n : Nat) :
    RelCT isa (LoopInv hH (s₀ := s₀) (s₀' := s₀') n) H.body fun s s' =>
      isa.eval .ne s = isa.eval .ne s' ∧
      (isa.eval .ne s = some false → Inv hH s₀ 0 s ∧ Inv hH s₀' 0 s') ∧
      (isa.eval .ne s = some true → ∃ m < n, LoopInv hH (s₀ := s₀) (s₀' := s₀') m s s') := by
  have hlt := nn_lt (s₀ := s₀)
  by_cases hn : 1 ≤ n ∧ n ≤ nn s₀
  · have b := (body_rel hH hp hp' hz hq hc hn.1 (by omega)).mono (P' := LoopInv hH (s₀ := s₀) (s₀' := s₀') n)
      (fun _ _ (h : LoopInv hH (s₀ := s₀) (s₀' := s₀') n _ _) => ⟨h.2.2.1.kr, h.2.2.2.kr⟩)
      fun _ _ h => h
    refine (b.wp (F₁ := fun (t : State) => Inv hH s₀ (n - 1) t ∧ t.zf = some (decide (n - 1 = 0)))
      (F₂ := fun (t : State) => Inv hH s₀' (n - 1) t ∧ t.zf = some (decide (n - 1 = 0)))
      fun s s' (h : LoopInv hH (s₀ := s₀) (s₀' := s₀') n _ _) =>
        ⟨body_ok hH hp hz hn.1 (by omega) h.2.2.1, body_ok hH hp' hz hn.1 (by omega) h.2.2.2⟩).mono
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
    RelCT isa (fun s s' => (Inv hH s₀ (nn s₀) s ∧ s.zf = some (decide (nn s₀ = 0))) ∧
        (Inv hH s₀' (nn s₀') s' ∧ s'.zf = some (decide (nn s₀' = 0))))
      (.ite .e (.block []) (.loop H.body .ne)) fun s s' => Inv hH s₀ 0 s ∧ Inv hH s₀' 0 s' := by
  have hN := hq.nn
  refine RelCT.ite (fun s s' h => by simp [eval, h.1.2, h.2.2, hN]) ?_ ?_
  · refine ((RelCT.taint (A := taint) (Taint.ofRegs []) (fun _ _ _ => Taint.agree_ofRegs (by simp))
      (c := .block []) (by taint_decide)).wp (F₁ := Inv hH s₀ 0) (F₂ := Inv hH s₀' 0)
      fun s s' h => ?_).mono (fun _ _ h => h) fun _ _ h => h.2
    have e : nn s₀ = 0 := by simpa [eval, h.1.1.2] using h.2
    have e' : nn s₀' = 0 := hN ▸ e
    exact ⟨WP.block_nil (e ▸ h.1.1.1), WP.block_nil (e' ▸ h.1.2.1)⟩
  · refine (RelCT.loop (M := isa) (LoopInv hH (s₀ := s₀) (s₀' := s₀')) (step_rel hH hp hp' hz hq hc)
      (nn s₀)).mono (fun s s' h => ?_) fun _ _ h => h
    have e : nn s₀ ≠ 0 := by simpa [eval, h.1.1.2] using h.2
    exact ⟨by omega, (Nat.le_refl _), h.1.1.1, hN ▸ h.1.2.1⟩

theorem ct (hc : Checks H) : RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') H.iterate fun _ _ => True := by
  have hN := hq.nn
  have pro := rel_taint (F := fun s => s = s₀) (F' := fun s => s = s₀')
    (G := fun s => Inv hH s₀ (nn s₀) s ∧ s.zf = some (decide (nn s₀ = 0)))
    (G' := fun s => Inv hH s₀' (nn s₀') s ∧ s.zf = some (decide (nn s₀' = 0)))
    args (fun s s' e e' r hr => by
        rw [e, e']
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl
        · exact hq.rdi
        · exact hq.rsi
        · exact hq.rcx
        · exact hq.r8
        · exact hq.rsp) hc.pro
    (fun _ e => by rw [e]; exact pro_ok hH hp hz) (fun _ e => by rw [e]; exact pro_ok hH hp' hz)
  obtain ⟨_, hr⟩ := hc.restore
  have restore : RelCT isa (fun s s' => Inv hH s₀ 0 s ∧ Inv hH s₀' 0 s') (.block (restore H.P))
      fun _ _ => True :=
    RelCT.taint (A := taint) (Taint.ofRegs kregs) (fun _ _ h => Taint.agree_ofRegs (kr_agree hq h.1.kr h.2.kr)) hr
  exact pro.seq ((loop_rel hH hp hp' hz hq hc).seq restore)

end

/-- `iterate` is verified against `iterG`, given the taint checks and the
facts about its code that the kernel checks for each hash function. -/
theorem verified {H : Hash} (hH : HashOK H) (hc : Checks H)
    (hmx : H.iterate.allInstrs (fun i => !loadsMxcsr i) = true)
    (hsat : ∃ s, (iterG hH.SH H.W).pre s) :
    Verified X86_64.target H.iterate (iterG hH.SH H.W) := by
  have hz := hH.sizes
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, hsat⟩
  · obtain ⟨t, s', he, hg, hpost⟩ := correct hH (pre_of hH hs) hz
    exact ⟨t, s', he, abiPreserved_of_exec hmx he hg, hpost⟩
  · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hpub
    exact (ct hH (pre_of hH h₁) (pre_of hH h₂) hz ⟨h1, h2, h3, h4, h5, h6⟩ hc
      _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.Pbkdf2.Md.X86_64
