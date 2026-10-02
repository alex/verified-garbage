import VerifiedGarbage.Proof.Scrypt.X86_64.Whole.Correct
import VerifiedGarbage.Proof.Framework.X86_64.Taint

/-!
# scrypt on x86-64: constant time, up to the indices `j`

Two runs whose public data agree have the same layout, so between the frame's
push and pop they are related by `Two`: both satisfy `Ctx` with that layout
(and `Φ`, what the next piece needs), whatever their secrets, and the indices
of all the scryptROMix calls agree (`LeakEq`, from the contract's leakage).
The blocks address only the stack, from `rsp` (the taint analysis); each call
is of constant-time code whose public data agree (`RelCT.callEx`): for PBKDF2
its pointers and lengths, for scryptROMix also the indices of its block, which
`LeakEq` gives (`leak_X`); the loop's branch agrees since both runs count the
same blocks.
-/

namespace VG.Proof.Scrypt.X86_64.Whole

open VG VG.X86_64 VG.Impl.Scrypt.X86_64
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

/-- What each of two runs has, between the frame's push and pop. -/
abbrev Env := Lay × (Reg → BitVec 64) × (Reg → BitVec 64) × Mem × Mem

/-- Two runs with the same layout, each satisfying `Ctx` and `Φ`. -/
def Two (Φ : Lay → Mem → State → Prop) (a b : State) : Prop :=
  ∃ e : Env, e.1.Ok ∧ LeakEq e.1 e.2.2.2.1 e.2.2.2.2 ∧ Ctx e.1 e.2.1 e.2.2.2.1 a ∧
    Ctx e.1 e.2.2.1 e.2.2.2.2 b ∧ Φ e.1 e.2.2.2.1 a ∧ Φ e.1 e.2.2.2.2 b

/-- Code whose runs leak the same, and which keeps `Ctx` and establishes `Ψ`. -/
theorem two_wp {c : Prog isa} {Φ Ψ : Lay → Mem → State → Prop}
    (hct : RelCT isa (Two Φ) c fun _ _ => True)
    (hw : ∀ (L : Lay) g m₀ (t : State), L.Ok → Ctx L g m₀ t → Φ L m₀ t →
      WP isa c t fun t' => Ctx L g m₀ t' ∧ Ψ L m₀ t') :
    RelCT isa (Two Φ) c (Two Ψ) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨ht, -⟩ := hct _ _ _ _ _ _ hp e₁ e₂
  obtain ⟨⟨L, g₁, g₂, m₁, m₂⟩, hL, hk, c₁, c₂, f₁, f₂⟩ := hp
  obtain ⟨_, u₁, x₁, y₁⟩ := hw L g₁ m₁ s₁ hL c₁ f₁
  obtain ⟨_, u₂, x₂, y₂⟩ := hw L g₂ m₂ s₂ hL c₂ f₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ x₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ x₂
  exact ⟨ht, ⟨L, g₁, g₂, m₁, m₂⟩, hL, hk, y₁.1, y₂.1, y₁.2, y₂.2⟩

theorem rsp_two {L : Lay} {t₁ t₂ : State} {g₁ g₂ : Reg → BitVec 64} {m₁ m₂ : Mem}
    (c₁ : Ctx L g₁ m₁ t₁) (c₂ : Ctx L g₂ m₂ t₂) : t₁.gpr .rsp = t₂.gpr .rsp :=
  c₁.rsp.trans c₂.rsp.symm

/-- A block whose addresses depend only on `rsp`, with what it establishes. -/
theorem two_blk {is : List Instr} {Φ Ψ : Lay → Mem → State → Prop}
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (h : (taint.check (Taint.ofRegs [.rsp]) (.block is) hc).isSome = true)
    (hw : ∀ (L : Lay) g m₀ (t : State), L.Ok → Ctx L g m₀ t → Φ L m₀ t →
      WP isa (.block is) t fun t' => Ctx L g m₀ t' ∧ Ψ L m₀ t') :
    RelCT isa (Two Φ) (.block is) (Two Ψ) :=
  two_wp (RelCT.taint (A := taint) (Taint.ofRegs [.rsp])
    (fun _ _ ⟨_, _, _, c₁, c₂, _, _⟩ => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact rsp_two c₁ c₂) h) hw

/-- A call of verified code, with the same regions in both runs, after which
`Ψ` holds. -/
theorem two_call {n : String} {c : Prog isa} {k : Contract isa} {Φ Ψ : Lay → Mem → State → Prop}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hct : ConstantTime isa k.pre k.pub c) (rd wr : Lay → List Region)
    (hpre : ∀ (L : Lay) g m₀ (t : State), L.Ok → Ctx L g m₀ t → Φ L m₀ t →
      k.pre (t.callEntry.withRegions (rd L) (wr L)))
    (hpub : ∀ (L : Lay) t₁ t₂ g₁ g₂ m₁ m₂, L.Ok → LeakEq L m₁ m₂ → Ctx L g₁ m₁ t₁ → Ctx L g₂ m₂ t₂ →
      Φ L m₁ t₁ → Φ L m₂ t₂ →
      k.pub (t₁.callEntry.withRegions (rd L) (wr L)) (t₂.callEntry.withRegions (rd L) (wr L)))
    (hsub : ∀ (L : Lay) m₀ (t : State), L.Ok → Φ L m₀ t → ∀ r ∈ rd L ++ wr L, ∃ R ∈ L.regions, Within r R)
    (hwsub : ∀ (L : Lay) m₀ (t : State), L.Ok → Φ L m₀ t → ∀ r ∈ wr L, InBuf L r)
    (hw : ∀ (L : Lay) g m₀ (t : State), L.Ok → Ctx L g m₀ t → Φ L m₀ t →
      WP isa (.call n c) t fun t' => Ctx L g m₀ t' ∧ Ψ L m₀ t') :
    RelCT isa (Two Φ) (.call n c) (Two Ψ) :=
  two_wp (RelCT.callEx hv hct fun _ _ ⟨⟨L, _⟩, hL, hk, c₁, c₂, f₁, f₂⟩ =>
    ⟨rd L, wr L, rd L, wr L, hpre _ _ _ _ hL c₁ f₁, hpre _ _ _ _ hL c₂ f₂,
      hpub _ _ _ _ _ _ _ hL hk c₁ c₂ f₁ f₂, (covers c₁ (hsub L _ _ hL f₁) (hwsub L _ _ hL f₁)).1,
      (covers c₁ (hsub L _ _ hL f₁) (hwsub L _ _ hL f₁)).2,
      (covers c₂ (hsub L _ _ hL f₂) (hwsub L _ _ hL f₂)).1,
      (covers c₂ (hsub L _ _ hL f₂) (hwsub L _ _ hL f₂)).2, rsp_two c₁ c₂⟩) hw

/-! ## The calls -/

theorem pbk_pub_two {L : Lay} (hL : L.Ok) {g₁ g₂ : Reg → BitVec 64} {m₁ m₂ : Mem} {t₁ t₂ : State}
    (c₁ : Ctx L g₁ m₁ t₁) (c₂ : Ctx L g₂ m₂ t₂) {salt : Addr} {sl : BitVec 64} {out : Addr}
    {ol : BitVec 64} (a₁ : PbkArgs L salt sl out ol t₁) (a₂ : PbkArgs L salt sl out ol t₂) :
    pbkK.pub (t₁.callEntry.withRegions (pbkRd L salt sl) (pbkWr L out ol))
      (t₂.callEntry.withRegions (pbkRd L salt sl) (pbkWr L out ol)) := by
  simp only [pbkK, Proof.Pbkdf2.Md.X86_64.pbkG, gpr_ce _ _ _ (by decide : Reg.rdi ≠ .rsp),
    gpr_ce _ _ _ (by decide : Reg.rsi ≠ .rsp), gpr_ce _ _ _ (by decide : Reg.rdx ≠ .rsp),
    gpr_ce _ _ _ (by decide : Reg.rcx ≠ .rsp), gpr_ce _ _ _ (by decide : Reg.r8 ≠ .rsp),
    gpr_ce _ _ _ (by decide : Reg.r9 ≠ .rsp), a₁.rdi, a₁.rsi, a₁.rdx, a₁.rcx, a₁.r8, a₁.r9, a₂.rdi,
    a₂.rsi, a₂.rdx, a₂.rcx, a₂.r8, a₂.r9, pbk_e0 hL c₁ a₁, pbk_e0 hL c₂ a₂, pbk_e1 hL c₁ a₁,
    pbk_e1 hL c₂ a₂, c₁.ce_rsp, c₂.ce_rsp, and_self]

/-- The block ROMix works on in iteration `i`, on entry to it. -/
theorem romix_bytes {L : Lay} (hL : L.Ok) {g : Reg → BitVec 64} {m₀ : Mem} {t : State}
    (hc : Ctx L g m₀ t) {i : Nat} (hi : i < L.pp) (hb : InvB L m₀ i t) (rd wr : List Region) :
    bytesAt (t.callEntry.withRegions rd wr).mem (blkAt L i) (128 * L.r.toNat) = X L m₀ i := by
  rw [State.withRegions_mem, ce_bytesAt t (by
      rw [hc.ret]; exact hL.stk_in (by omega) (by simpa [Nat.mul_comm] using blk_in hL hi))
    (by have := hL.blen_lt; have := blk_le hL hi; omega), hb.blks i hi]
  simp only [Nat.lt_irrefl, ite_false]

theorem romix_pub_two {L : Lay} (hL : L.Ok) {g₁ g₂ : Reg → BitVec 64} {m₁ m₂ : Mem} {t₁ t₂ : State}
    (hk : LeakEq L m₁ m₂) (c₁ : Ctx L g₁ m₁ t₁) (c₂ : Ctx L g₂ m₂ t₂) {i : Nat} (hi : i < L.pp)
    (b₁ : InvB L m₁ i t₁) (b₂ : InvB L m₂ i t₂) (a₁ : RomixArgs L (blkAt L i) t₁)
    (a₂ : RomixArgs L (blkAt L i) t₂) :
    Proof.Scrypt.roMixX86_64.pub (t₁.callEntry.withRegions [] (romixWr L i))
      (t₂.callEntry.withRegions [] (romixWr L i)) := by
  simp only [Proof.Scrypt.roMixX86_64, gpr_ce _ _ _ (by decide : Reg.rdi ≠ .rsp),
    gpr_ce _ _ _ (by decide : Reg.rsi ≠ .rsp), gpr_ce _ _ _ (by decide : Reg.rdx ≠ .rsp),
    gpr_ce _ _ _ (by decide : Reg.rcx ≠ .rsp), gpr_ce _ _ _ (by decide : Reg.r8 ≠ .rsp),
    gpr_ce _ _ _ (by decide : Reg.r9 ≠ .rsp), a₁.rdi, a₁.rsi, a₁.rdx, a₁.rcx, a₁.r8, a₁.r9, a₂.rdi,
    a₂.rsi, a₂.rdx, a₂.rcx, a₂.r8, a₂.r9, c₁.ce_rsp, c₂.ce_rsp, true_and,
    romix_bytes hL c₁ hi b₁, romix_bytes hL c₂ hi b₂]
  exact leak_X hk hi

/-! ## The pieces -/

/-- Iteration `pp - n` of the loop is next. -/
abbrev LoopAt (n : Nat) (L : Lay) (m₀ : Mem) (t : State) : Prop :=
  0 < n ∧ n ≤ L.pp ∧ InvB L m₀ (L.pp - n) t

theorem body_ct (n : Nat) :
    RelCT isa (Two (LoopAt n)) (.seq (.block romixArgs) (.seq (.call "vg_scrypt_romix"
      Impl.Scrypt.X86_64.roMix) (.block nextBlock)))
      (Two fun L m₀ t => 0 < n ∧ n ≤ L.pp ∧ InvB L m₀ (L.pp - n + 1) t ∧
        t.zf = some (decide (L.pp - n + 1 = L.pp))) := by
  have a : RelCT isa (Two (LoopAt n)) (.block romixArgs) (Two fun L m₀ t => 0 < n ∧ n ≤ L.pp ∧
      InvB L m₀ (L.pp - n) t ∧ RomixArgs L (blkAt L (L.pp - n)) t) :=
    two_blk (by taint_decide) fun _ _ _ _ hL hc ⟨h0, hn, hb⟩ =>
      WP.mono (romixArgs_ok hL hc hb.cur) fun _ ⟨hc', hm, ha⟩ =>
        ⟨hc', h0, hn, ⟨by rw [hm]; exact hb.cur, by rw [hm]; exact hb.blks⟩, ha⟩
  have b : RelCT isa (Two fun L m₀ t => 0 < n ∧ n ≤ L.pp ∧ InvB L m₀ (L.pp - n) t ∧
      RomixArgs L (blkAt L (L.pp - n)) t) (.call "vg_scrypt_romix" Impl.Scrypt.X86_64.roMix)
      (Two fun L m₀ t => 0 < n ∧ n ≤ L.pp ∧ Mid L m₀ (L.pp - n) t) :=
    two_call RoMix.roMix_correct RoMix.roMix_ct (fun _ => []) (fun L => romixWr L (L.pp - n))
      (fun _ _ _ _ hL hc ⟨h0, hn, _, ha⟩ => romix_pre hL hc (by omega) ha)
      (fun _ _ _ _ _ _ _ hL hk c₁ c₂ ⟨h0, hn, b₁, a₁⟩ ⟨_, _, b₂, a₂⟩ =>
        romix_pub_two hL hk c₁ c₂ (by omega) b₁ b₂ a₁ a₂)
      (fun _ _ _ hL ⟨h0, hn, _⟩ => romix_sub hL (by omega))
      (fun _ _ _ hL ⟨h0, hn, _⟩ => romix_wsub hL (by omega))
      (fun _ _ _ _ hL hc ⟨h0, hn, hb, ha⟩ =>
        WP.mono (call_step hL (by omega) hc hb ha) fun _ ⟨hc', hm⟩ => ⟨hc', h0, hn, hm⟩)
  have c : RelCT isa (Two fun L m₀ t => 0 < n ∧ n ≤ L.pp ∧ Mid L m₀ (L.pp - n) t) (.block nextBlock)
      (Two fun L m₀ t => 0 < n ∧ n ≤ L.pp ∧ InvB L m₀ (L.pp - n + 1) t ∧
        t.zf = some (decide (L.pp - n + 1 = L.pp))) :=
    two_blk (by taint_decide) fun _ _ _ _ hL hc ⟨h0, hn, hm⟩ =>
      WP.mono (next_step hL (by omega) hc hm) fun _ ⟨hc', hb, hz⟩ => ⟨hc', h0, hn, hb, hz⟩
  exact a.seq (b.seq c)

theorem loop_ct :
    RelCT isa (Two fun L m₀ t => InvB L m₀ 0 t) romixLoop (Two fun L m₀ t => InvB L m₀ L.pp t) := by
  have ev : ∀ x : State, isa.eval .ne x = x.zf.map (!·) := fun _ => rfl
  have h := fun n => RelCT.loop (M := isa) (c := .ne) (Q := Two fun L m₀ t => InvB L m₀ L.pp t)
    (fun n => Two (LoopAt n)) (fun n => (body_ct n).mono (fun _ _ h => h) fun a b hab => by
      obtain ⟨e, hL, hk, c₁, c₂, ⟨h0, hn, b₁, z₁⟩, ⟨-, -, b₂, z₂⟩⟩ := hab
      rw [ev, ev, z₁, z₂]
      refine ⟨rfl, fun hf => ?_, fun ht => ?_⟩
      · have hl : e.1.pp - n + 1 = e.1.pp := by simpa using hf
        exact ⟨e, hL, hk, c₁, c₂, show InvB e.1 _ e.1.pp a from hl ▸ b₁,
          show InvB e.1 _ e.1.pp b from hl ▸ b₂⟩
      · have hl : e.1.pp - n + 1 ≠ e.1.pp := by simpa using ht
        have e₁ : e.1.pp - (n - 1) = e.1.pp - n + 1 := by omega
        exact ⟨n - 1, by omega, e, hL, hk, c₁, c₂, ⟨by omega, by omega, e₁ ▸ b₁⟩,
          ⟨by omega, by omega, e₁ ▸ b₂⟩⟩) n
  refine (RelCT.exists_ h).mono (fun a b ⟨e, hL, hk, c₁, c₂, b₁, b₂⟩ => ⟨e.1.pp, e, hL, hk, c₁, c₂,
    ⟨hL.pp_pos, Nat.le_refl _, by rw [Nat.sub_self]; exact b₁⟩,
    ⟨hL.pp_pos, Nat.le_refl _, by rw [Nat.sub_self]; exact b₂⟩⟩) fun _ _ h => h

/-! ## The whole function -/

section
variable {pbk : Prog isa} (hv : Verified X86_64.target pbk (Spec.Hmac.sha256I.pbkdf2Contract X86_64.abi 24))
  (hsp : NoSp pbk) (hd : pbk.depth ≤ 3) (name : String)
include hv hsp hd

theorem scryptBody_ct : RelCT isa (Two fun L _ t => Entry L t) (scryptBody name pbk) fun _ _ => True := by
  have p1a : RelCT isa (Two fun L _ t => Entry L t) (.block pbk1Args)
      (Two fun L _ t => PbkArgs L L.salt L.sl L.b (BitVec.ofNat 64 (L.blen.toNat * 128)) t) :=
    two_blk (by taint_decide) fun _ _ _ _ hL hc he =>
      WP.mono (pbk1Args_ok hL hc he) fun _ ⟨hc', ha, _⟩ => ⟨hc', ha⟩
  have p1c : RelCT isa (Two fun L _ t => PbkArgs L L.salt L.sl L.b (BitVec.ofNat 64 (L.blen.toNat * 128)) t)
      (.call name pbk)
      (Two fun L m₀ t => ∀ k < L.pp, bytesAt t.mem (blkAt L k) (128 * L.r.toNat) = X L m₀ k) :=
    two_call (pbk_correct hv) (pbk_ct hv) (fun L => pbkRd L L.salt L.sl)
      (fun L => pbkWr L L.b (BitVec.ofNat 64 (L.blen.toNat * 128)))
      (fun _ _ _ _ hL hc ha => pbk_pre' hL hc ha (pbk1_regions hL))
      (fun _ _ _ _ _ _ _ hL _ c₁ c₂ a₁ a₂ => pbk_pub_two hL c₁ c₂ a₁ a₂)
      (fun _ _ _ hL _ => pbk_sub hL (pbk1_regions hL)) (fun _ _ _ hL _ => pbk_wsub hL (pbk1_regions hL))
      (fun _ _ _ _ hL hc ha =>
        WP.mono (pbk1_call_ok hv hsp hd name hL hc ha) fun _ ⟨hc', _, hx⟩ => ⟨hc', hx⟩)
  have c0 : RelCT isa (Two fun L m₀ t => ∀ k < L.pp, bytesAt t.mem (blkAt L k) (128 * L.r.toNat) = X L m₀ k)
      (.block cur0) (Two fun L m₀ t => InvB L m₀ 0 t) :=
    two_blk (by taint_decide) fun _ _ _ _ hL hc hx => start_ok hL hc hx
  have p2a : RelCT isa (Two fun L m₀ t => InvB L m₀ L.pp t) (.block pbk2Args)
      (Two fun L _ t => PbkArgs L L.b (BitVec.ofNat 64 (L.blen.toNat * 128)) L.out L.ol t) :=
    two_blk (by taint_decide) fun _ _ _ _ hL hc _ =>
      WP.mono (pbk2Args_ok hL hc) fun _ ⟨hc', ha, _⟩ => ⟨hc', ha⟩
  have p2c : RelCT isa (Two fun L _ t => PbkArgs L L.b (BitVec.ofNat 64 (L.blen.toNat * 128)) L.out L.ol t)
      (.call name pbk) (Two fun _ _ _ => True) :=
    two_call (pbk_correct hv) (pbk_ct hv) (fun L => pbkRd L L.b (BitVec.ofNat 64 (L.blen.toNat * 128)))
      (fun L => pbkWr L L.out L.ol)
      (fun _ _ _ _ hL hc ha => pbk_pre' hL hc ha (pbk2_regions hL))
      (fun _ _ _ _ _ _ _ hL _ c₁ c₂ a₁ a₂ => pbk_pub_two hL c₁ c₂ a₁ a₂)
      (fun _ _ _ hL _ => pbk_sub hL (pbk2_regions hL)) (fun _ _ _ hL _ => pbk_wsub hL (pbk2_regions hL))
      (fun _ _ _ _ hL hc ha =>
        WP.mono (pbk_call hv hsp hd name hL hc ha (pbk2_regions hL)) fun _ h => ⟨h.1, trivial⟩)
  exact ((p1a.seq p1c).seq (c0.seq (loop_ct.seq (p2a.seq p2c)))).mono (fun _ _ h => h)
    fun _ _ _ => trivial

theorem scrypt_ct :
    ConstantTime isa Proof.Scrypt.scryptX86_64.pre Proof.Scrypt.scryptX86_64.pub (scrypt name pbk) := by
  refine RelCT.constantTime (RelCT.frame (fun _ _ h => h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    (RelCT.mono (scryptBody_ct hv hsp hd name) ?_ fun _ _ _ => trivial))
  rintro _ _ ⟨s₁, s₂, ⟨h₁, h₂, hdi, hsi, hdx, hcx, h8, h9, a0, a1, a2, a3, a4, a5, a6, hsp', hlk⟩, rfl, rfl⟩
  have e : lay s₂ = lay s₁ := by
    simp only [lay, hdi, hsi, hdx, hcx, h8, h9, a0, a1, a2, a3, a4, a5, a6, hsp']
  refine ⟨⟨lay s₁, s₁.gpr, s₂.gpr, s₁.mem, s₂.mem⟩, lay_ok h₁, ?_, push_ctx h₁, e ▸ push_ctx h₂,
    push_entry s₁, e ▸ push_entry s₂⟩
  rw [← hdi, ← hsi, ← hdx, ← hcx, ← h8, ← a0, ← a2] at hlk
  exact hlk

end

end VG.Proof.Scrypt.X86_64.Whole
