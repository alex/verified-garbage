import VerifiedGarbage.Proof.Scrypt.AArch64.Whole.Correct
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.AArch64.Taint

/-!
# scrypt on AArch64: constant time, up to the indices `j`

Untrusted: everything here is checked by Lean. As on x86-64
(`Proof/Scrypt/X86_64/Whole/CT.lean`): two runs whose public data agree
have the same layout, so between the frames' pushes and pops they are
related by `Two`: both satisfy `Ctx` with that layout (and `Φ`, what the
next piece needs), whatever their secrets, and the indices of all the
scryptROMix calls agree (`LeakEq`). The blocks address only the stack, from
`sp` (the taint analysis); each call is of constant-time code whose public
data agree (`RelCT.call`); the loop's branch agrees since both runs count
the same blocks. The frames leak only `sp` (`frame_ct`, `alloc_ct`).
-/

namespace VG.Proof.Scrypt.AArch64.Whole

open VG VG.AArch64 VG.Impl.Scrypt.AArch64
open VG.Spec.Scrypt (bytesAt roMixIndices)

/-- The indices of every scryptROMix agree in two runs from `m₁` and `m₂`. -/
def LeakEq (L : Lay) (m₁ m₂ : Mem) : Prop :=
  (Spec.Scrypt.blocks (bytesAt m₁ L.pw L.pwl.toNat) (bytesAt m₁ L.salt L.sl.toNat) L.r.toNat L.pp).flatMap
      (roMixIndices L.r.toNat L.NN) =
    (Spec.Scrypt.blocks (bytesAt m₂ L.pw L.pwl.toNat) (bytesAt m₂ L.salt L.sl.toNat) L.r.toNat L.pp).flatMap
      (roMixIndices L.r.toNat L.NN)

theorem leak_X {L : Lay} {m₁ m₂ : Mem} (h : LeakEq L m₁ m₂) {k : Nat} (hk : k < L.pp) :
    roMixIndices L.r.toNat L.NN (X L m₁ k) = roMixIndices L.r.toNat L.NN (X L m₂ k) := by
  have h₁ : k < (Spec.Scrypt.blocks (bytesAt m₁ L.pw L.pwl.toNat) (bytesAt m₁ L.salt L.sl.toNat)
      L.r.toNat L.pp).length := by rw [Whole.blocks_length]; exact hk
  have h₂ : k < (Spec.Scrypt.blocks (bytesAt m₂ L.pw L.pwl.toNat) (bytesAt m₂ L.salt L.sl.toNat)
      L.r.toNat L.pp).length := by rw [Whole.blocks_length]; exact hk
  simp only [X, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h₁, List.getElem?_eq_getElem h₂,
    Option.getD_some]
  exact Whole.indices_eq h h₁ h₂

/-- The layout of two runs, and what each has on entry. -/
structure Env where
  L : Lay
  g₁ : Reg → BitVec 64
  g₂ : Reg → BitVec 64
  v₁ : VReg → BitVec 128
  v₂ : VReg → BitVec 128
  m₁ : Mem
  m₂ : Mem

/-- Two runs with the same layout, each satisfying `Ctx` and `Φ`. -/
def Two (Φ : Lay → Mem → State → Prop) (a b : State) : Prop :=
  ∃ e : Env, e.L.Ok ∧ LeakEq e.L e.m₁ e.m₂ ∧ Ctx e.L e.g₁ e.v₁ e.m₁ a ∧ Ctx e.L e.g₂ e.v₂ e.m₂ b ∧
    Φ e.L e.m₁ a ∧ Φ e.L e.m₂ b

/-- Code whose runs leak the same, and which keeps `Ctx` and establishes `Ψ`. -/
theorem two_wp {c : Prog isa} {Φ Ψ : Lay → Mem → State → Prop}
    (hct : RelCT isa (Two Φ) c fun _ _ => True)
    (hw : ∀ (L : Lay) g vv m₀ (t : State), L.Ok → Ctx L g vv m₀ t → Φ L m₀ t →
      WP isa c t fun t' => Ctx L g vv m₀ t' ∧ Ψ L m₀ t') :
    RelCT isa (Two Φ) c (Two Ψ) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨ht, -⟩ := hct _ _ _ _ _ _ hp e₁ e₂
  obtain ⟨e, hL, hk, c₁, c₂, f₁, f₂⟩ := hp
  obtain ⟨_, u₁, x₁, y₁⟩ := hw _ _ _ _ s₁ hL c₁ f₁
  obtain ⟨_, u₂, x₂, y₂⟩ := hw _ _ _ _ s₂ hL c₂ f₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ x₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ x₂
  exact ⟨ht, e, hL, hk, y₁.1, y₂.1, y₁.2, y₂.2⟩

theorem sp_two {L : Lay} {t₁ t₂ : State} {g₁ g₂ : Reg → BitVec 64} {v₁ v₂ : VReg → BitVec 128}
    {m₁ m₂ : Mem} (c₁ : Ctx L g₁ v₁ m₁ t₁) (c₂ : Ctx L g₂ v₂ m₂ t₂) : t₁.sp = t₂.sp :=
  c₁.sp.trans c₂.sp.symm

/-- A block whose addresses depend only on `sp`, with what it establishes. -/
theorem two_blk {is : List Instr} {Φ Ψ : Lay → Mem → State → Prop}
    {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (h : (taint.check (Taint.ofRegs []) (.block is) hc).isSome = true)
    (hw : ∀ (L : Lay) g vv m₀ (t : State), L.Ok → Ctx L g vv m₀ t → Φ L m₀ t →
      WP isa (.block is) t fun t' => Ctx L g vv m₀ t' ∧ Ψ L m₀ t') :
    RelCT isa (Two Φ) (.block is) (Two Ψ) :=
  two_wp (RelCT.taint (A := taint) (Taint.ofRegs [])
    (fun _ _ ⟨_, _, _, c₁, c₂, _, _⟩ => ⟨sp_two c₁ c₂, fun _ hr => False.elim (by simp at hr)⟩) h) hw

/-- A call of verified code, with the same regions in both runs, after which
`Ψ` holds. -/
theorem two_call {n : String} {c : Prog isa} {k : Contract isa} {Φ Ψ : Lay → Mem → State → Prop}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hct : ConstantTime isa k.pre k.pub c) (rd wr : Lay → List Region)
    (hpre : ∀ (L : Lay) g vv m₀ (t : State), L.Ok → Ctx L g vv m₀ t → Φ L m₀ t →
      k.pre (t.callEntry.withRegions (rd L) (wr L)))
    (hpub : ∀ (L : Lay) t₁ t₂ g₁ g₂ v₁ v₂ m₁ m₂, L.Ok → LeakEq L m₁ m₂ → Ctx L g₁ v₁ m₁ t₁ →
      Ctx L g₂ v₂ m₂ t₂ → Φ L m₁ t₁ → Φ L m₂ t₂ →
      k.pub (t₁.callEntry.withRegions (rd L) (wr L)) (t₂.callEntry.withRegions (rd L) (wr L)))
    (hsub : ∀ (L : Lay) m₀ (t : State), L.Ok → Φ L m₀ t → ∀ r ∈ rd L ++ wr L, ∃ R ∈ L.regions, Within r R)
    (hwsub : ∀ (L : Lay) m₀ (t : State), L.Ok → Φ L m₀ t → ∀ r ∈ wr L, InBuf L r)
    (hw : ∀ (L : Lay) g vv m₀ (t : State), L.Ok → Ctx L g vv m₀ t → Φ L m₀ t →
      WP isa (.call n c) t fun t' => Ctx L g vv m₀ t' ∧ Ψ L m₀ t') :
    RelCT isa (Two Φ) (.call n c) (Two Ψ) :=
  two_wp (fun s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂ => by
    obtain ⟨e, hL, hk, c₁, c₂, f₁, f₂⟩ := hp
    have w₁ := covers c₁ (hsub _ _ _ hL f₁) (hwsub _ _ _ hL f₁)
    have w₂ := covers c₂ (hsub _ _ _ hL f₂) (hwsub _ _ _ hL f₂)
    exact RelCT.call (n := n) hv hct (P := fun a b => a = s₁ ∧ b = s₂) (rd e.L) (wr e.L)
      (fun _ _ ⟨h₁, h₂⟩ => by
        subst h₁ h₂
        exact ⟨hpre _ _ _ _ _ hL c₁ f₁, hpre _ _ _ _ _ hL c₂ f₂,
          hpub _ _ _ _ _ _ _ _ _ hL hk c₁ c₂ f₁ f₂, w₁.1, w₁.2, w₂.1, w₂.2⟩)
      _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂) hw

/-! ## The calls -/

theorem pbk_pub_two {L : Lay} {g₁ g₂ : Reg → BitVec 64} {v₁ v₂ : VReg → BitVec 128} {m₁ m₂ : Mem}
    {t₁ t₂ : State} (c₁ : Ctx L g₁ v₁ m₁ t₁) (c₂ : Ctx L g₂ v₂ m₂ t₂) {salt : Addr} {sl : BitVec 64}
    {out : Addr} {ol : BitVec 64} (a₁ : PbkArgs L salt sl out ol t₁) (a₂ : PbkArgs L salt sl out ol t₂) :
    pbkK.pub (t₁.callEntry.withRegions (pbkRd L salt sl) (pbkWr L out ol))
      (t₂.callEntry.withRegions (pbkRd L salt sl) (pbkWr L out ol)) := by
  simp only [pbkK, Proof.Pbkdf2.Md.AArch64.pbkG, gpr_ce _ _ _ (by decide : Reg.x0 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.x1 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.x2 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.x3 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.x4 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.x5 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.x6 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.x7 ∉ linkRegs), a₁.x0, a₁.x1, a₁.x2, a₁.x3, a₁.x4, a₁.x5, a₁.x6,
    a₁.x7, a₂.x0, a₂.x1, a₂.x2, a₂.x3, a₂.x4, a₂.x5, a₂.x6, a₂.x7, c₁.ce_sp, c₂.ce_sp, and_self]

/-- The block ROMix works on in iteration `i`, on entry to it. -/
theorem romix_bytes {L : Lay} {m₀ : Mem} {t : State} {i : Nat} (hi : i < L.pp) (hb : InvB L m₀ i t) (rd wr : List Region) :
    bytesAt (t.callEntry.withRegions rd wr).mem (blkAt L i) (128 * L.r.toNat) = X L m₀ i := by
  rw [State.withRegions_mem, State.callEntry_mem, hb.blks i hi]
  simp only [Nat.lt_irrefl, ite_false]

theorem romix_pub_two {L : Lay} {g₁ g₂ : Reg → BitVec 64} {v₁ v₂ : VReg → BitVec 128}
    {m₁ m₂ : Mem} {t₁ t₂ : State} (hk : LeakEq L m₁ m₂) (c₁ : Ctx L g₁ v₁ m₁ t₁)
    (c₂ : Ctx L g₂ v₂ m₂ t₂) {i : Nat} (hi : i < L.pp) (b₁ : InvB L m₁ i t₁) (b₂ : InvB L m₂ i t₂)
    (a₁ : RomixArgs L (blkAt L i) t₁) (a₂ : RomixArgs L (blkAt L i) t₂) :
    Proof.Scrypt.roMixAArch64.pub (t₁.callEntry.withRegions [] (romixWr L i))
      (t₂.callEntry.withRegions [] (romixWr L i)) := by
  simp only [Proof.Scrypt.roMixAArch64, gpr_ce _ _ _ (by decide : Reg.x0 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.x1 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.x2 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.x3 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.x4 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.x5 ∉ linkRegs), a₁.x0, a₁.x1, a₁.x2, a₁.x3, a₁.x4, a₁.x5, a₂.x0,
    a₂.x1, a₂.x2, a₂.x3, a₂.x4, a₂.x5, c₁.ce_sp, c₂.ce_sp, true_and,
    romix_bytes hi b₁, romix_bytes hi b₂]
  exact leak_X hk hi

/-! ## The pieces -/

/-- Iteration `pp - n` of the loop is next. -/
abbrev LoopAt (n : Nat) (L : Lay) (m₀ : Mem) (t : State) : Prop :=
  0 < n ∧ n ≤ L.pp ∧ InvB L m₀ (L.pp - n) t

theorem body_ct (n : Nat) :
    RelCT isa (Two (LoopAt n)) (.seq (.block romixArgs) (.seq (.call "vg_scrypt_romix"
      Impl.Scrypt.AArch64.roMix) (.block nextBlock)))
      (Two fun L m₀ t => 0 < n ∧ n ≤ L.pp ∧ InvB L m₀ (L.pp - n + 1) t ∧
        (t.gpr .x11 != 0) = decide (L.pp - n + 1 ≠ L.pp)) := by
  have a : RelCT isa (Two (LoopAt n)) (.block romixArgs) (Two fun L m₀ t => 0 < n ∧ n ≤ L.pp ∧
      InvB L m₀ (L.pp - n) t ∧ RomixArgs L (blkAt L (L.pp - n)) t) :=
    two_blk (by taint_decide) fun _ _ _ _ _ hL hc ⟨h0, hn, hb⟩ =>
      WP.mono (romixArgs_ok hL hc hb.cur) fun _ ⟨hc', hm, ha⟩ =>
        ⟨hc', h0, hn, ⟨by rw [hm]; exact hb.cur, by rw [hm]; exact hb.blks⟩, ha⟩
  have b : RelCT isa (Two fun L m₀ t => 0 < n ∧ n ≤ L.pp ∧ InvB L m₀ (L.pp - n) t ∧
      RomixArgs L (blkAt L (L.pp - n)) t) (.call "vg_scrypt_romix" Impl.Scrypt.AArch64.roMix)
      (Two fun L m₀ t => 0 < n ∧ n ≤ L.pp ∧ Mid L m₀ (L.pp - n) t) :=
    two_call RoMix.roMix_correct RoMix.roMix_ct (fun _ => []) (fun L => romixWr L (L.pp - n))
      (fun _ _ _ _ _ hL hc ⟨h0, hn, _, ha⟩ => romix_pre hL hc (by omega) ha)
      (fun _ _ _ _ _ _ _ _ _ _ hk c₁ c₂ ⟨h0, hn, b₁, a₁⟩ ⟨_, _, b₂, a₂⟩ =>
        romix_pub_two hk c₁ c₂ (by omega) b₁ b₂ a₁ a₂)
      (fun _ _ _ hL ⟨h0, hn, _⟩ => romix_sub hL (by omega))
      (fun _ _ _ hL ⟨h0, hn, _⟩ => romix_wsub hL (by omega))
      (fun _ _ _ _ _ hL hc ⟨h0, hn, hb, ha⟩ =>
        WP.mono (call_step hL (by omega) hc hb ha) fun _ ⟨hc', hm⟩ => ⟨hc', h0, hn, hm⟩)
  have c : RelCT isa (Two fun L m₀ t => 0 < n ∧ n ≤ L.pp ∧ Mid L m₀ (L.pp - n) t) (.block nextBlock)
      (Two fun L m₀ t => 0 < n ∧ n ≤ L.pp ∧ InvB L m₀ (L.pp - n + 1) t ∧
        (t.gpr .x11 != 0) = decide (L.pp - n + 1 ≠ L.pp)) :=
    two_blk (by taint_decide) fun _ _ _ _ _ hL hc ⟨h0, hn, hm⟩ =>
      WP.mono (next_step hL (by omega) hc hm) fun _ ⟨hc', hb, hz⟩ => ⟨hc', h0, hn, hb, hz⟩
  exact a.seq (b.seq c)

theorem loop_ct :
    RelCT isa (Two fun L m₀ t => InvB L m₀ 0 t) romixLoop (Two fun L m₀ t => InvB L m₀ L.pp t) := by
  have ev : ∀ x : State, isa.eval (.nonzero .x .x11) x = some (x.gpr .x11 != 0) := fun x =>
    Proof.MdStream.AArch64.eval_nonzero x .x11
  have h := fun n => RelCT.loop (M := isa) (c := .nonzero .x .x11)
    (Q := Two fun L m₀ t => InvB L m₀ L.pp t)
    (fun n => Two (LoopAt n)) (fun n => (body_ct n).mono (fun _ _ h => h) fun a b hab => by
      obtain ⟨e, hL, hk, c₁, c₂, ⟨h0, hn, b₁, z₁⟩, ⟨-, -, b₂, z₂⟩⟩ := hab
      rw [ev, ev, z₁, z₂]
      refine ⟨rfl, fun hf => ?_, fun ht => ?_⟩
      · have hl : e.L.pp - n + 1 = e.L.pp := by simpa using hf
        exact ⟨e, hL, hk, c₁, c₂, show InvB e.L _ e.L.pp a from hl ▸ b₁,
          show InvB e.L _ e.L.pp b from hl ▸ b₂⟩
      · have hl : e.L.pp - n + 1 ≠ e.L.pp := by simpa using ht
        have e₁ : e.L.pp - (n - 1) = e.L.pp - n + 1 := by omega
        exact ⟨n - 1, by omega, e, hL, hk, c₁, c₂, ⟨by omega, by omega, e₁ ▸ b₁⟩,
          ⟨by omega, by omega, e₁ ▸ b₂⟩⟩) n
  refine (RelCT.exists_ h).mono (fun a b ⟨e, hL, hk, c₁, c₂, b₁, b₂⟩ => ⟨e.L.pp, e, hL, hk, c₁, c₂,
    ⟨hL.pp_pos, Nat.le_refl _, by rw [Nat.sub_self]; exact b₁⟩,
    ⟨hL.pp_pos, Nat.le_refl _, by rw [Nat.sub_self]; exact b₂⟩⟩) fun _ _ h => h

/-! ## The frames -/

/-- A frame saving a register leaks only `sp`. -/
theorem frame_ct {r r' : Reg} {body : Prog isa} {P R : State → State → Prop}
    (hsp : ∀ a b, P a b → a.sp = b.sp)
    (hb : RelCT isa (fun a b => ∃ s t, P s t ∧ a = pushed r s ∧ b = pushed r t) body R) :
    RelCT isa P (.frame (.push r) body (.pop r')) fun _ _ => True := by
  intro s t ts tt s' t' hp es et
  have push_eq : ∀ {a b : State}, isa.push (.push r) a = some b → b = pushed r a := by
    intro a b h
    simp only [isa, push] at h
    split at h <;> cases h
    rfl
  cases es with
  | frame ps bs qs =>
    cases et with
    | frame pt bt qt =>
      have ea := push_eq ps
      have eb := push_eq pt
      subst ea eb
      obtain ⟨rfl, _⟩ := hb _ _ _ _ _ _ ⟨s, t, hp, rfl, rfl⟩ bs bt
      have sp₁ := (Exec.rdwr bs).2.2
      have sp₂ := (Exec.rdwr bt).2.2
      have he := hsp s t hp
      refine ⟨?_, trivial⟩
      simp only [addrs, sp₁, sp₂, pushed, he]

/-- Allocating and freeing a buffer leaks nothing. -/
theorem alloc_ct {bytes : Nat} {body : Prog isa} {P R : State → State → Prop}
    (hb : RelCT isa (fun a b => ∃ s t, P s t ∧ a = allocated bytes s ∧ b = allocated bytes t) body R) :
    RelCT isa P (.frame (.alloc bytes) body (.free bytes)) fun _ _ => True := by
  intro s t ts tt s' t' hp es et
  have alloc_eq : ∀ {a b : State}, isa.push (.alloc bytes) a = some b → b = allocated bytes a := by
    intro a b h
    simp only [isa, push] at h
    split at h <;> cases h
    rfl
  cases es with
  | frame ps bs qs =>
    cases et with
    | frame pt bt qt =>
      have ea := alloc_eq ps
      have eb := alloc_eq pt
      subst ea eb
      obtain ⟨rfl, _⟩ := hb _ _ _ _ _ _ ⟨s, t, hp, rfl, rfl⟩ bs bt
      exact ⟨rfl, trivial⟩

/-! ## The whole function -/

/-- Two calls whose public data agree, in the inner frame. -/
def Entered (a b : State) : Prop :=
  ∃ s₁ s₂, Proof.Scrypt.scryptAArch64.pre s₁ ∧ Proof.Scrypt.scryptAArch64.pre s₂ ∧
    Proof.Scrypt.scryptAArch64.pub s₁ s₂ ∧ a = entered s₁ ∧ b = entered s₂

theorem save_ct : RelCT isa Entered (.block saveArgs) (Two fun L _ t => Entry L t) := by
  intro a b ta tb a' b' ⟨s₁, s₂, h₁, h₂, hp, ea, eb⟩ e₁ e₂
  subst ea eb
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, a0, a1, a2, a3, a4, hsp, hlk⟩ := hp
  have ht := (RelCT.taint (A := taint) (P := fun x y => x.sp = y.sp) (Taint.ofRegs [])
    (fun _ _ h => ⟨h, fun _ hr => False.elim (by simp at hr)⟩) (by taint_decide)
    _ _ _ _ _ _ (by show (entered s₁).sp = (entered s₂).sp; rw [entered_sp, entered_sp]; simp only [lay, hsp]) e₁ e₂).1
  obtain ⟨_, u₁, x₁, y₁⟩ := entry_ok h₁
  obtain ⟨_, u₂, x₂, y₂⟩ := entry_ok h₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ x₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ x₂
  have e : lay s₂ = lay s₁ := by
    simp only [lay, h0, h1, h2, h3, h4, h5, h6, h7, a0, a1, a2, a3, a4, hsp]
  refine ⟨ht, ⟨lay s₁, s₁.gpr, s₂.gpr, s₁.v, s₂.v, s₁.mem, s₂.mem⟩, lay_ok h₁, ?_, y₁.1, e ▸ y₂.1, y₁.2,
    e ▸ y₂.2⟩
  rw [← h0, ← h1, ← h2, ← h3, ← h4, ← h6, ← a0] at hlk
  exact hlk

section
variable {pbk : Prog isa} (hv : Verified AArch64.target pbk (Spec.Hmac.sha256I.pbkdf2Contract AArch64.abi 16))
  (hd : pbk.aarch64Depth ≤ 1) (name : String)
include hv hd

theorem rest_ct : RelCT isa (Two fun L _ t => Entry L t)
    (.seq (pbkCall name pbk pbk1Args) (.seq (.block cur0) (.seq romixLoop (pbkCall name pbk pbk2Args))))
    fun _ _ => True := by
  have p1a : RelCT isa (Two fun L _ t => Entry L t) (.block pbk1Args)
      (Two fun L _ t => PbkArgs L L.salt L.sl L.b (BitVec.ofNat 64 (L.blen.toNat * 128)) t) :=
    two_blk (by taint_decide) fun _ _ _ _ _ hL hc he =>
      WP.mono (pbk1Args_ok hL hc he) fun _ ⟨hc', _, ha⟩ => ⟨hc', ha⟩
  have p1c : RelCT isa (Two fun L _ t => PbkArgs L L.salt L.sl L.b (BitVec.ofNat 64 (L.blen.toNat * 128)) t)
      (.call name pbk)
      (Two fun L m₀ t => ∀ k < L.pp, bytesAt t.mem (blkAt L k) (128 * L.r.toNat) = X L m₀ k) :=
    two_call (pbk_correct hv) (pbk_ct hv) (fun L => pbkRd L L.salt L.sl)
      (fun L => pbkWr L L.b (BitVec.ofNat 64 (L.blen.toNat * 128)))
      (fun _ _ _ _ _ hL hc ha => pbk_pre' hL hc ha (pbk1_regions hL))
      (fun _ _ _ _ _ _ _ _ _ _ _ c₁ c₂ a₁ a₂ => pbk_pub_two c₁ c₂ a₁ a₂)
      (fun _ _ _ hL _ => pbk_sub hL (pbk1_regions hL)) (fun _ _ _ hL _ => pbk_wsub hL (pbk1_regions hL))
      (fun _ _ _ _ _ hL hc ha =>
        WP.mono (pbk1_call_ok hv hd name hL hc ha) fun _ ⟨hc', _, hx⟩ => ⟨hc', hx⟩)
  have c0 : RelCT isa (Two fun L m₀ t => ∀ k < L.pp, bytesAt t.mem (blkAt L k) (128 * L.r.toNat) = X L m₀ k)
      (.block cur0) (Two fun L m₀ t => InvB L m₀ 0 t) :=
    two_blk (by taint_decide) fun _ _ _ _ _ hL hc hx => start_ok hL hc hx
  have p2a : RelCT isa (Two fun L m₀ t => InvB L m₀ L.pp t) (.block pbk2Args)
      (Two fun L _ t => PbkArgs L L.b (BitVec.ofNat 64 (L.blen.toNat * 128)) L.out L.ol t) :=
    two_blk (by taint_decide) fun _ _ _ _ _ hL hc _ =>
      WP.mono (pbk2Args_ok hL hc) fun _ ⟨hc', _, ha⟩ => ⟨hc', ha⟩
  have p2c : RelCT isa (Two fun L _ t => PbkArgs L L.b (BitVec.ofNat 64 (L.blen.toNat * 128)) L.out L.ol t)
      (.call name pbk) (Two fun _ _ _ => True) :=
    two_call (pbk_correct hv) (pbk_ct hv) (fun L => pbkRd L L.b (BitVec.ofNat 64 (L.blen.toNat * 128)))
      (fun L => pbkWr L L.out L.ol)
      (fun _ _ _ _ _ hL hc ha => pbk_pre' hL hc ha (pbk2_regions hL))
      (fun _ _ _ _ _ _ _ _ _ _ _ c₁ c₂ a₁ a₂ => pbk_pub_two c₁ c₂ a₁ a₂)
      (fun _ _ _ hL _ => pbk_sub hL (pbk2_regions hL)) (fun _ _ _ hL _ => pbk_wsub hL (pbk2_regions hL))
      (fun _ _ _ _ _ hL hc ha =>
        WP.mono (pbk_call hv hd name hL hc ha (pbk2_regions hL)) fun _ h => ⟨h.1, trivial⟩)
  exact ((p1a.seq p1c).seq (c0.seq (loop_ct.seq (p2a.seq p2c)))).mono (fun _ _ h => h)
    fun _ _ _ => trivial

theorem scrypt_ct :
    ConstantTime isa Proof.Scrypt.scryptAArch64.pre Proof.Scrypt.scryptAArch64.pub (scrypt name pbk) := by
  refine RelCT.constantTime (frame_ct (fun _ _ h => h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    (alloc_ct (R := fun _ _ => True) ?_))
  refine (save_ct.seq (rest_ct hv hd name)).mono ?_ fun _ _ _ => trivial
  rintro _ _ ⟨_, _, ⟨s₁, s₂, ⟨h₁, h₂, hp⟩, rfl, rfl⟩, rfl, rfl⟩
  exact ⟨s₁, s₂, h₁, h₂, hp, rfl, rfl⟩

end

end VG.Proof.Scrypt.AArch64.Whole
