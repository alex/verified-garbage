import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Iterate

/-!
# PBKDF2-HMAC's iteration over a Merkle–Damgård hash function on x86 (32-bit): constant time

Untrusted: everything here is checked by Lean. As for the streaming-level
functions (`Proof/Hmac/Generic/X86/`): the pieces between the calls are
checked by the taint analysis, those that read the arguments on the stack
(the prologue, and the end of a step, which loads `t`) with the arguments
public (`argTaint`); the calls of the compression function are related by
`cmp_rel`, from its contract. Then `iterate` is verified against the
contract with the arguments read only (`iterG`), and with them writable
(`iterW`).
-/

namespace VG.Proof.Pbkdf2.Md.X86.Iterate

open VG.X86
open VG.Impl.Pbkdf2.Md.X86 (Hash)
open VG.Proof.Pbkdf2.Md.X86
open VG.Proof.Hmac.Generic.X86 (HashOK iterG iterW argTaint ArgsOut agree_argTaint rel_agree rel_wp stk)
open VG.Proof.Sha256.X86.Stream (eval_e eval_ne)
open Spec.Sha256 (bytesAt)

/-- The registers `KR` fixes. -/
abbrev pubRegs : List Reg := [.esp, .ebp, .ebx, .esi, .edi]

/-- The taint checks of the pieces of `iterate` between its calls. -/
structure Checks (H : Hash) : Prop where
  pro : ∃ hc, (VG.Taint.check taint (argTaint [] (4 + 4 * 5)) (.block H.prologue) hc).isSome = true
  load : ∃ hc, (VG.Taint.check taint (τr pubRegs) (.block (H.loadKey 0 ++ H.atBlk)) hc).isSome = true
  mid : ∃ hc, (VG.Taint.check taint (τr pubRegs) (.block (H.digest ++ H.loadKey H.S ++ H.atBlk)) hc).isSome = true
  tail : ∃ hc, (VG.Taint.check taint (argTaint [.ebp, .ebx, .esi, .edi] (4 + 4 * 5))
    (.block (H.digest ++ H.tStep)) hc).isSome = true
  restore : ∃ hc, (VG.Taint.check taint (τr [.ebp]) (.block H.st.restore) hc).isSome = true

theorem skip_check : ∃ hc, (VG.Taint.check taint (τr []) (.block []) hc).isSome = true :=
  ⟨_, by taint_decide⟩

/-- The public arguments are the same. -/
structure PubEq (s₀ s₀' : State) : Prop where
  esp : s₀.gpr .esp = s₀'.gpr .esp
  args : ∀ i < 5, arg s₀ i = arg s₀' i

/-- What the pieces keep, and the padding. -/
structure KP (H : Hash) (sc : Nat) (s₀ : State) (m : Nat) (s : State) : Prop extends KR H sc s₀ m s where
  pad : bytesAt s.mem ((hv H s₀).setWidth 64 + BitVec.ofNat 64 (H.N + H.D)) (H.B - H.D) = H.tailB

/-! ## Each piece, in one run -/

section
variable {H : Hash} (hO : MdOk H) {sc : Nat} {s₀ : State} (hp : Pre H sc s₀)
include hO hp

theorem b1_ok {m : Nat} {s : State} (h : KP H sc s₀ m s) :
    WP isa (.block (H.loadKey 0 ++ H.atBlk)) s fun t =>
      KP H sc s₀ m t ∧ t.gpr .eax = hv H s₀ + BitVec.ofNat 32 H.N := by
  rw [← List.append_nil (H.loadKey 0 ++ H.atBlk)]
  have := bounds hp
  refine load_ok hO hp (by have := hp.hz.S; omega) h.toKR fun s₂ k₂ ax₂ f₁ _ => WP.block_nil ⟨⟨k₂, ?_⟩, ax₂⟩
  rw [Memory.frame_bytesAt f₁ (fun r hr => blk_disj hp (by omega) (by omega) r (by
    simp only [List.mem_singleton] at hr; simp [hr])) (by omega), h.pad]

theorem c_ok {m : Nat} {s : State} (h : KP H sc s₀ m s) (hax : s.gpr .eax = hv H s₀ + BitVec.ofNat 32 H.N) :
    WP isa H.cmp s (KP H sc s₀ m) := by
  have := bounds hp
  refine cmpS_ok hO hp h.toKR hax fun s₃ k₃ f₃ _ => ⟨k₃, ?_⟩
  rw [Memory.frame_bytesAt f₃ (blk_disj hp (by omega) (by omega)) (by omega), h.pad]

theorem b2_ok {m : Nat} {s : State} (h : KP H sc s₀ m s) :
    WP isa (.block (H.digest ++ H.loadKey H.S ++ H.atBlk)) s fun t =>
      KP H sc s₀ m t ∧ t.gpr .eax = hv H s₀ + BitVec.ofNat 32 H.N := by
  obtain ⟨hb, hf, hw, hso, hW, hN0, hN, hD0, hDN, hB, hB64, hS⟩ := bounds hp
  have := hv_toNat hp; have := hp.hz.DL
  have sbB : Region.Sub ⟨(hv H s₀).setWidth 64 + BitVec.ofNat 64 H.N, H.B⟩ (scR sc s₀) :=
    fun a ha => hvR_sub hp a (Offset.sub_base _ (by omega) a ha)
  rw [List.append_assoc]
  refine digest_ok hp.hz hO.out h.ebx (by omega) (cov_hv hp h.wr) h.pad fun s₃ g₃ rd₃ wr₃ f₃ _ p₃ => ?_
  have k₃ : KR H sc s₀ m s₃ := h.toKR.write rd₃ wr₃ g₃ f₃
    ((save_hv hp (Nat.le_refl _)).sub_right (Offset.sub_base _ (by omega))) ⟨scR sc s₀, by simp, sbB⟩
  rw [← List.append_nil (H.loadKey H.S ++ H.atBlk)]
  refine load_ok hO hp (by omega) k₃ fun s₂ k₂ ax₂ f₁ _ => WP.block_nil ⟨⟨k₂, ?_⟩, ax₂⟩
  rw [Memory.frame_bytesAt f₁ (fun r hr => blk_disj hp (by omega) (by omega) r (by
    simp only [List.mem_singleton] at hr; simp [hr])) (by omega), p₃]

theorem b3_ok {m : Nat} (hm : 1 ≤ m) (hn : m < 2 ^ 32) {s : State} (h : KP H sc s₀ m s) :
    WP isa (.block (H.digest ++ H.tStep)) s fun t => KP H sc s₀ (m - 1) t ∧ t.zf = some (decide (m - 1 = 0)) :=
  tail_ok hO hp hm hn h.toKR h.pad fun _ k z _ p _ _ => ⟨⟨k, p⟩, z⟩

end

/-! ## Two runs -/

variable {H : Hash} (hO : MdOk H) {sc : Nat}
variable {s₀ s₀' : State} (hp : Pre H sc s₀) (hp' : Pre H sc s₀') (hq : PubEq s₀ s₀')

theorem PubEq.nn (hq : PubEq s₀ s₀') : nn s₀ = nn s₀' := by
  show (arg s₀ 2).toNat = (arg s₀' 2).toNat; rw [hq.args 2 (by decide)]

theorem eqs (hq : PubEq s₀ s₀') : scr s₀' = scr s₀ ∧ hv H s₀' = hv H s₀ :=
  ⟨(hq.args 4 (by decide)).symm, by rw [hv, hv, scr, scr, hq.args 4 (by decide)]⟩

theorem kr_agree (hq : PubEq s₀ s₀') {m : Nat} {s s' : State} (h : KR H sc s₀ m s)
    (h' : KR H sc s₀' m s') : ∀ r ∈ pubRegs, s.gpr r = s'.gpr r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · rw [h.esp, h'.esp, E, E, hq.esp]
  · rw [h.ebp, h'.ebp, (eqs (H := H) hq).1]
  · rw [h.ebx, h'.ebx, (eqs (H := H) hq).2]
  · rw [h.esi, h'.esi, key, key, hq.args 0 (by decide)]
  · rw [h.edi, h'.edi]

/-- The arguments lie outside the writable regions. -/
theorem args_out {t : State} (h : Pre H sc t) {s : State} (hsp : s.gpr .esp = E t) (hwr : s.wr = t.wr) :
    ArgsOut 5 s := by
  have e : (⟨(s.gpr .esp).setWidth 64, 4 + 4 * 5⟩ : Region) = ⟨(E t).setWidth 64, 4 + 20⟩ := by rw [hsp]
  refine ⟨by rw [hsp]; exact h.spf, ?_⟩
  rw [e, hwr, h.wr]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact Taint.frame_disjoint (by have := h.spf; omega) h.r_t h.a_t
  · exact Taint.frame_disjoint (by have := h.spf; omega) h.r_s h.a_s

include hO hp hp' hq

/-- A call of the compression function, in both runs. -/
theorem cmp_rel' {m : Nat} :
    RelCT isa (fun s s' => (KP H sc s₀ m s ∧ s.gpr .eax = hv H s₀ + BitVec.ofNat 32 H.N) ∧
        (KP H sc s₀' m s' ∧ s'.gpr .eax = hv H s₀' + BitVec.ofNat 32 H.N)) H.cmp
      fun s s' => KP H sc s₀ m s ∧ KP H sc s₀' m s' := by
  obtain ⟨e4, ehv⟩ := eqs (H := H) hq
  have hB : 0 < H.B := by have := hp.hz.B4; omega
  exact rel_wp (cmp_rel hO.comp hB (sp := E s₀) fun s s' ⟨⟨k, a⟩, ⟨k', a'⟩⟩ =>
      ⟨cmpArgs hp k.toKR a, by have := cmpArgs hp' k'.toKR a'; rwa [e4, ehv] at this, k.esp,
        by rw [k'.esp, E, E, hq.esp]⟩)
    (fun _ ⟨k, a⟩ => c_ok hO hp k a) (fun _ ⟨k, a⟩ => c_ok hO hp' k a)

theorem body_rel (hc : Checks H) {m : Nat} (hm : 1 ≤ m) (hn : m < 2 ^ 32) :
    RelCT isa (fun s s' => KP H sc s₀ m s ∧ KP H sc s₀' m s') H.body
      fun s s' => (KP H sc s₀ (m - 1) s ∧ s.zf = some (decide (m - 1 = 0))) ∧
        (KP H sc s₀' (m - 1) s' ∧ s'.zf = some (decide (m - 1 = 0))) := by
  have b1 := rel_agree (F := KP H sc s₀ m) (F' := KP H sc s₀' m) (τr pubRegs) (fun _ _ h h' => agree_regs (kr_agree hq h.toKR h'.toKR)) hc.load
    (fun _ h => b1_ok hO hp h) (fun _ h => b1_ok hO hp' h)
  have b2 := rel_agree (F := KP H sc s₀ m) (F' := KP H sc s₀' m) (τr pubRegs) (fun _ _ h h' => agree_regs (kr_agree hq h.toKR h'.toKR)) hc.mid
    (fun _ h => b2_ok hO hp h) (fun _ h => b2_ok hO hp' h)
  have b3 := rel_agree (F := KP H sc s₀ m) (F' := KP H sc s₀' m) (argTaint [.ebp, .ebx, .esi, .edi] (4 + 4 * 5)) (fun s s' k k' =>
      agree_argTaint (fun r hr => kr_agree hq k.toKR k'.toKR r (by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; tauto))
        (kr_agree hq k.toKR k'.toKR .esp (by simp)) (args_out hp k.esp k.wr) (args_out hp' k'.esp k'.wr)
        fun j hj => by rw [k.toKR.argEq hp hj, k'.toKR.argEq hp' hj, hq.args j hj]) hc.tail
    (fun _ h => b3_ok hO hp hm hn h) (fun _ h => b3_ok hO hp' hm hn h)
  exact b1.seq ((cmp_rel' hO hp hp' hq).seq (b2.seq ((cmp_rel' hO hp hp' hq).seq b3)))

/-- The loop's invariant in two runs, with `n` steps left. -/
abbrev LoopInv (n : Nat) (s s' : State) : Prop :=
  1 ≤ n ∧ n ≤ nn s₀ ∧ KP H sc s₀ n s ∧ KP H sc s₀' n s'

theorem step_rel (hc : Checks H) (n : Nat) :
    RelCT isa (LoopInv (H := H) (sc := sc) (s₀ := s₀) (s₀' := s₀') n) H.body fun s s' =>
      isa.eval .ne s = isa.eval .ne s' ∧
      (isa.eval .ne s = some false → KP H sc s₀ 0 s ∧ KP H sc s₀' 0 s') ∧
      (isa.eval .ne s = some true → ∃ m < n, LoopInv (H := H) (sc := sc) (s₀ := s₀) (s₀' := s₀') m s s') := by
  have hlt : nn s₀ < 2 ^ 32 := (arg s₀ 2).isLt
  by_cases hn : 1 ≤ n ∧ n ≤ nn s₀
  · refine ((body_rel hO hp hp' hq hc hn.1 (by omega)).mono
      (P' := LoopInv (H := H) (sc := sc) (s₀ := s₀) (s₀' := s₀') n) (fun _ _ h => ⟨h.2.2.1, h.2.2.2⟩)
      fun _ _ h => h).mono (fun _ _ h => h) fun t t' h => ?_
    obtain ⟨⟨i, z⟩, ⟨i', z'⟩⟩ := h
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
    RelCT isa (fun s s' => (KP H sc s₀ (nn s₀) s ∧ s.zf = some (decide (nn s₀ = 0))) ∧
        (KP H sc s₀' (nn s₀') s' ∧ s'.zf = some (decide (nn s₀' = 0))))
      (.ite .e (.block []) (.loop H.body .ne))
      fun s s' => KP H sc s₀ 0 s ∧ KP H sc s₀' 0 s' := by
  have hN := hq.nn
  have ev : ∀ {t : State} {k : Nat}, t.zf = some (decide (k = 0)) → isa.eval .e t = some (decide (k = 0)) :=
    fun h => by show eval .e _ = _; rw [eval_e, h]
  refine RelCT.ite (fun s s' h => by rw [ev h.1.2, ev h.2.2, hN]) ?_ ?_
  · by_cases e : nn s₀ = 0
    · have e' : nn s₀' = 0 := hN ▸ e
      exact (rel_agree (c := .block [])
        (F := fun s => KP H sc s₀ (nn s₀) s ∧ s.zf = some (decide (nn s₀ = 0)))
        (F' := fun s => KP H sc s₀' (nn s₀') s ∧ s.zf = some (decide (nn s₀' = 0)))
        (G := KP H sc s₀ 0) (G' := KP H sc s₀' 0) (τr [])
        (fun s s' h h' => agree_regs (by simp)) skip_check
        (fun s h => WP.block_nil (e ▸ h.1)) (fun s h => WP.block_nil (e' ▸ h.1))).mono (fun _ _ h => h.1)
        fun _ _ h => h
    · intro _ _ _ _ _ _ h
      have z := h.2
      rw [ev h.1.1.2] at z
      exact absurd (by simpa using z) e
  · refine (RelCT.loop (M := isa) (LoopInv (H := H) (sc := sc) (s₀ := s₀) (s₀' := s₀'))
      (step_rel hO hp hp' hq hc) (nn s₀)).mono (fun s s' h => ?_) fun _ _ h => h
    have z := h.2
    rw [ev h.1.1.2] at z
    have e : nn s₀ ≠ 0 := by simpa using z
    exact ⟨by omega, Nat.le_refl _, h.1.1.1, hN ▸ h.1.2.1⟩

theorem ct (hc : Checks H) : RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') H.iterate fun _ _ => True := by
  have hN := hq.nn
  have pro := rel_agree (F := fun s => s = s₀) (F' := fun s => s = s₀')
    (G := fun s => KP H sc s₀ (nn s₀) s ∧ s.zf = some (decide (nn s₀ = 0)))
    (G' := fun s => KP H sc s₀' (nn s₀') s ∧ s.zf = some (decide (nn s₀' = 0)))
    (argTaint [] (4 + 4 * 5)) (fun s s' e e' => by
        rw [e, e']
        exact agree_argTaint (fun r hr => nomatch hr) hq.esp (args_out hp rfl rfl) (args_out hp' rfl rfl)
          hq.args) hc.pro
    (fun _ e => by rw [e]; exact WP.mono (pro_ok hO hp) fun _ ⟨h, z⟩ => ⟨⟨h.toKR, h.pad⟩, z⟩)
    (fun _ e => by rw [e]; exact WP.mono (pro_ok hO hp') fun _ ⟨h, z⟩ => ⟨⟨h.toKR, h.pad⟩, z⟩)
  obtain ⟨_, hr⟩ := hc.restore
  have restore : RelCT isa (fun s s' => KP H sc s₀ 0 s ∧ KP H sc s₀' 0 s') (.block H.st.restore)
      fun _ _ => True :=
    RelCT.taint (A := taint) (τr [.ebp]) (fun _ _ h => agree_regs fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact kr_agree hq h.1.toKR h.2.toKR .ebp (by simp)) hr
  exact pro.seq ((loop_rel hO hp hp' hq hc).seq restore)

end VG.Proof.Pbkdf2.Md.X86.Iterate

namespace VG.Proof.Pbkdf2.Md.X86.Iterate

open VG.X86
open VG.Impl.Pbkdf2.Md.X86 (Hash)
open VG.Proof.Pbkdf2.Md.X86
open VG.Proof.Hmac.Generic.X86 (iterG iterW)

/-- `iterate` is verified against `iterG`, given the taint checks, which the
kernel evaluates for each hash function. -/
theorem verified {H : Hash} (hO : MdOk H) {sc : Nat} (hc : Checks H)
    (hfit : H.st.buf + H.N + H.B ≤ 8 * sc) (hsat : ∃ s, (iterG hO.hH.SH sc).pre s) :
    Verified X86.target H.iterate (iterG hO.hH.SH sc) := by
  refine ⟨fun s hs => correct hO (pre_of hO.hH hs hO.sizes hfit), fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, hsat⟩
  obtain ⟨h1, h2⟩ := hpub
  exact (ct hO (pre_of hO.hH h₁ hO.sizes hfit) (pre_of hO.hH h₂ hO.sizes hfit) ⟨h1, h2⟩ hc
    _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-- The regions `iterate` reads and writes, of those `iterW` gives it. -/
def narrowRd (S D : Nat) (s : State) : List Region :=
  [⟨(arg s 0).setWidth 64, 2 * S⟩, ⟨(arg s 1).setWidth 64, D⟩, ⟨argAddr s 0, 20⟩]
def narrowWr (D sc : Nat) (s : State) : List Region :=
  [⟨(arg s 3).setWidth 64, D⟩, ⟨(arg s 4).setWidth 64, 8 * sc⟩]

/-- `iterate` is verified against `iterW`, which lets it write its arguments:
the code only reads them. -/
theorem verifiedW {H : Hash} (hO : MdOk H) {sc : Nat} (hc : Checks H)
    (hfit : H.st.buf + H.N + H.B ≤ 8 * sc) (hsat : ∃ s, (iterW hO.hH.SH sc).pre s) :
    Verified X86.target H.iterate (iterW hO.hH.SH sc) := by
  have pre : ∀ s, (iterW hO.hH.SH sc).pre s → (iterG hO.hH.SH sc).pre
      (s.withRegions (narrowRd hO.hH.SH.stateBytes hO.hH.SH.digestBytes s) (narrowWr hO.hH.SH.digestBytes sc s)) := by
    intro s h
    obtain ⟨_, _, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩ := h
    simp only [iterG, narrowRd, narrowWr, arg_withRegions, argAddr_withRegions, State.withRegions_gpr,
      State.withRegions_rd, State.withRegions_wr]
    exact ⟨trivial, trivial, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  refine Verified.narrowTo (verified hO hc hfit (hsat.elim fun s hs => ⟨_, pre s hs⟩))
    (narrowRd hO.hH.SH.stateBytes hO.hH.SH.digestBytes) (narrowWr hO.hH.SH.digestBytes sc) pre (fun s h => ?_)
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

end VG.Proof.Pbkdf2.Md.X86.Iterate
