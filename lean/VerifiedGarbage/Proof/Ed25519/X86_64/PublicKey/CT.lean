import VerifiedGarbage.Proof.Ed25519.X86_64.PublicKey.Correct
import VerifiedGarbage.Proof.Framework.X86_64.Taint

/-!
# Ed25519 public-key derivation on x86-64: constant time

Untrusted: everything here is checked by Lean. Two runs whose pointers
agree have the same layout, so between the frame's push and pop they are
related by `Two`: both satisfy `Ctx` with that layout (and `Φ`, what the
next call needs of the registers), whatever their secrets. The blocks
address only the stack and, in `pkPrune`, `scratch`, from registers that
agree (the taint analysis); each call is of constant-time code whose public
data, its pointers, agree (`RelCT.callEx`).
-/

namespace VG.Proof.Ed25519.X86_64.PublicKey

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.Sha512.X86_64 (Compress)

/-- What each of two runs has, between the frame's push and pop. -/
abbrev Two.Env := Lay × (Reg → BitVec 64) × (Reg → BitVec 64) × BitVec 32 × BitVec 32 × Mem × Mem

/-- Two runs with the same layout, each satisfying `Ctx` and `Φ`. -/
def Two (Φ : Lay → State → Prop) (a b : State) : Prop :=
  ∃ e : Two.Env, e.1.Ok ∧ Ctx e.1 e.2.1 e.2.2.2.1 e.2.2.2.2.2.1 a ∧
    Ctx e.1 e.2.2.1 e.2.2.2.2.1 e.2.2.2.2.2.2 b ∧ Φ e.1 a ∧ Φ e.1 b

/-- Code whose runs leak the same, and which keeps `Ctx` and establishes `Ψ`. -/
theorem two_wp {c : Prog isa} {Φ Ψ : Lay → State → Prop}
    (hct : RelCT isa (Two Φ) c fun _ _ => True)
    (hw : ∀ (L : Lay) g mx m₀ (t : State), L.Ok → Ctx L g mx m₀ t → Φ L t →
      WP isa c t fun t' => Ctx L g mx m₀ t' ∧ Ψ L t') :
    RelCT isa (Two Φ) c (Two Ψ) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨ht, -⟩ := hct _ _ _ _ _ _ hp e₁ e₂
  obtain ⟨⟨L, g₁, g₂, mx₁, mx₂, m₁, m₂⟩, hL, c₁, c₂, f₁, f₂⟩ := hp
  obtain ⟨_, u₁, x₁, y₁⟩ := hw L g₁ mx₁ m₁ s₁ hL c₁ f₁
  obtain ⟨_, u₂, x₂, y₂⟩ := hw L g₂ mx₂ m₂ s₂ hL c₂ f₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ x₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ x₂
  exact ⟨ht, ⟨L, g₁, g₂, mx₁, mx₂, m₁, m₂⟩, hL, y₁.1, y₂.1, y₁.2, y₂.2⟩

/-- A block whose addresses depend only on the registers `rs`, which agree. -/
theorem two_block {is : List Instr} {Φ : Lay → State → Prop} (rs : List Reg)
    (hrs : ∀ L t₁ t₂ g₁ g₂ mx₁ mx₂ m₁ m₂, Ctx L g₁ mx₁ m₁ t₁ → Ctx L g₂ mx₂ m₂ t₂ → Φ L t₁ → Φ L t₂ →
      ∀ r ∈ rs, t₁.gpr r = t₂.gpr r)
    {hc : VG.Taint.Hint VG.X86_64.Taint.T} (h : (taint.check (Taint.ofRegs rs) (.block is) hc).isSome = true) :
    RelCT isa (Two Φ) (.block is) fun _ _ => True :=
  RelCT.taint (A := taint) (Taint.ofRegs rs)
    (fun _ _ ⟨_, _, c₁, c₂, f₁, f₂⟩ => Taint.agree_ofRegs (hrs _ _ _ _ _ _ _ _ _ c₁ c₂ f₁ f₂)) h

theorem rsp_two {L : Lay} {t₁ t₂ : State} {g₁ g₂ : Reg → BitVec 64} {mx₁ mx₂ : BitVec 32} {m₁ m₂ : Mem}
    (c₁ : Ctx L g₁ mx₁ m₁ t₁) (c₂ : Ctx L g₂ mx₂ m₂ t₂) : t₁.gpr .rsp = t₂.gpr .rsp :=
  c₁.rsp.trans c₂.rsp.symm

theorem covers {L : Lay} {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem} {t : State}
    (hc : Ctx L g mx m₀ t) {rd wr : List Region}
    (hsub : ∀ r ∈ rd ++ wr, ∃ R ∈ [L.SEED, L.FR, L.OUT, L.SCR], Within r R)
    (hwsub : ∀ r ∈ wr, Within r L.OUT ∨ Within r L.SCR) :
    Covers (rd ++ wr) (t.rd ++ t.wr) ∧ Covers wr t.wr := by
  refine ⟨Covers.of_sub fun r hr => ?_, Covers.of_sub fun r hr => ?_⟩
  · obtain ⟨R, hR, hw⟩ := hsub r hr
    exact ⟨R, by rw [hc.rd, hc.wr]; simpa using hR, hw⟩
  · rw [hc.wr]
    rcases hwsub r hr with h | h
    · exact ⟨_, by simp, h⟩
    · exact ⟨_, by simp, h⟩

/-- A call, with the same regions in both runs. -/
theorem two_call {n : String} {c : Prog isa} {k : Contract isa} {Φ : Lay → State → Prop}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hct : ConstantTime isa k.pre k.pub c) (rd wr : Lay → List Region)
    (hpre : ∀ (L : Lay) g mx m₀ (t : State), L.Ok → Ctx L g mx m₀ t → Φ L t →
      k.pre (t.callEntry.withRegions (rd L) (wr L)))
    (hpub : ∀ L t₁ t₂ g₁ g₂ mx₁ mx₂ m₁ m₂, Ctx L g₁ mx₁ m₁ t₁ → Ctx L g₂ mx₂ m₂ t₂ → Φ L t₁ → Φ L t₂ →
      k.pub (t₁.callEntry.withRegions (rd L) (wr L)) (t₂.callEntry.withRegions (rd L) (wr L)))
    (hsub : ∀ L, ∀ r ∈ rd L ++ wr L, ∃ R ∈ [L.SEED, L.FR, L.OUT, L.SCR], Within r R)
    (hwsub : ∀ L, ∀ r ∈ wr L, Within r L.OUT ∨ Within r L.SCR) :
    RelCT isa (Two Φ) (.call n c) fun _ _ => True :=
  RelCT.callEx hv hct fun _ _ ⟨⟨L, _⟩, hL, c₁, c₂, f₁, f₂⟩ =>
    ⟨rd L, wr L, rd L, wr L, hpre _ _ _ _ _ hL c₁ f₁, hpre _ _ _ _ _ hL c₂ f₂,
      hpub _ _ _ _ _ _ _ _ _ c₁ c₂ f₁ f₂, (covers c₁ (hsub L) (hwsub L)).1, (covers c₁ (hsub L) (hwsub L)).2,
      (covers c₂ (hsub L) (hwsub L)).1, (covers c₂ (hsub L) (hwsub L)).2, rsp_two c₁ c₂⟩

/-- A block, with what it establishes. -/
theorem two_blk {is : List Instr} {Φ Ψ : Lay → State → Prop} (rs : List Reg)
    (hrs : ∀ L t₁ t₂ g₁ g₂ mx₁ mx₂ m₁ m₂, Ctx L g₁ mx₁ m₁ t₁ → Ctx L g₂ mx₂ m₂ t₂ → Φ L t₁ → Φ L t₂ →
      ∀ r ∈ rs, t₁.gpr r = t₂.gpr r)
    {hc : VG.Taint.Hint VG.X86_64.Taint.T} (h : (taint.check (Taint.ofRegs rs) (.block is) hc).isSome = true)
    (hw : ∀ (L : Lay) g mx m₀ (t : State), L.Ok → Ctx L g mx m₀ t → Φ L t →
      WP isa (.block is) t fun t' => Ctx L g mx m₀ t' ∧ Ψ L t') :
    RelCT isa (Two Φ) (.block is) (Two Ψ) :=
  two_wp (two_block rs hrs h) hw

/-- A call of verified code, after which `Ctx` holds again. -/
theorem two_callP {n : String} {c : Prog isa} {k : Contract isa} {Φ : Lay → State → Prop}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hct : ConstantTime isa k.pre k.pub c) (hsp : NoSp c) (hd : c.depth ≤ 1) (rd wr : Lay → List Region)
    (hpre : ∀ (L : Lay) g mx m₀ (t : State), L.Ok → Ctx L g mx m₀ t → Φ L t →
      k.pre (t.callEntry.withRegions (rd L) (wr L)))
    (hpub : ∀ L t₁ t₂ g₁ g₂ mx₁ mx₂ m₁ m₂, Ctx L g₁ mx₁ m₁ t₁ → Ctx L g₂ mx₂ m₂ t₂ → Φ L t₁ → Φ L t₂ →
      k.pub (t₁.callEntry.withRegions (rd L) (wr L)) (t₂.callEntry.withRegions (rd L) (wr L)))
    (hsub : ∀ L, ∀ r ∈ rd L ++ wr L, ∃ R ∈ [L.SEED, L.FR, L.OUT, L.SCR], Within r R)
    (hwsub : ∀ L, ∀ r ∈ wr L, Within r L.OUT ∨ Within r L.SCR) :
    RelCT isa (Two Φ) (.call n c) (Two fun _ _ => True) :=
  two_wp (two_call hv hct rd wr hpre hpub hsub hwsub) fun L _ _ _ _ hL hc hf =>
    call_ok hL hv hsp hd hc (hpre _ _ _ _ _ hL hc hf) (hsub L) (hwsub L) fun _ hc' _ _ _ => ⟨hc', trivial⟩

theorem rspOnly {Φ : Lay → State → Prop} : ∀ (L : Lay) (t₁ t₂ : State) g₁ g₂ mx₁ mx₂ m₁ m₂,
    Ctx L g₁ mx₁ m₁ t₁ → Ctx L g₂ mx₂ m₂ t₂ → Φ L t₁ → Φ L t₂ → ∀ r ∈ [Reg.rsp], t₁.gpr r = t₂.gpr r := by
  intro L t₁ t₂ _ _ _ _ _ _ c₁ c₂ _ _ r hr
  simp only [List.mem_singleton] at hr; subst hr
  exact rsp_two c₁ c₂

/-- The frame's body, for any implementation `v` of the compression function. -/
theorem body_ct (v : Compress) :
    RelCT isa (Two fun _ _ => True) (pkBody v.callee v.suffix) fun _ _ => True := by
  -- `init`
  have i₁ : RelCT isa (Two fun _ _ => True) (.block pkInitArgs) (Two InitArgs) :=
    two_blk [.rsp] rspOnly (by taint_decide) fun _ _ _ _ _ _ hc _ =>
      WP.mono (initArgs_ok hc) fun _ ⟨hc', _, ha⟩ => ⟨hc', ha⟩
  have i₂ := two_callP (n := Spec.Sha512.init512Api.name) (Φ := InitArgs)
    (Proof.Sha512.X86_64.Stream.init_verified _).1 (Proof.Sha512.X86_64.Stream.init_verified _).2.1
    (nosp_init _) (by decide) (fun _ => initRd) initWr (fun _ _ _ _ _ hL hc ha => init_pre hL hc ha)
    (fun L t₁ t₂ _ _ _ _ _ _ _ _ a₁ a₂ =>
      ((gpr_ce t₁ initRd (initWr L) (by decide)).trans a₁).trans
        ((gpr_ce t₂ initRd (initWr L) (by decide)).trans a₂).symm)
    (fun _ => init_sub) (fun _ => init_wsub)
  -- `update`
  have u₁ : RelCT isa (Two fun _ _ => True) (.block pkUpdateArgs) (Two UpdArgs) :=
    two_blk [.rsp] rspOnly (by taint_decide) fun _ _ _ _ _ _ hc _ =>
      WP.mono (updArgs_ok hc) fun _ ⟨hc', _, ha⟩ => ⟨hc', ha⟩
  have u₂ := two_callP (n := Spec.Sha512.updateApi.name ++ v.suffix) (Φ := UpdArgs)
    (upd_verified v).1 (upd_verified v).2.1 (upd_nosp v) (upd_depth v) updRd updWr
    (fun _ _ _ _ _ hL hc ha => upd_pre hL hc ha)
    (fun L t₁ t₂ _ _ _ _ _ _ c₁ c₂ a₁ a₂ => by
      obtain ⟨d₁, s₁, x₁, c₁', r₁⟩ := upd_regs a₁ (updRd L) (updWr L)
      obtain ⟨d₂, s₂, x₂, c₂', r₂⟩ := upd_regs a₂ (updRd L) (updWr L)
      exact ⟨d₁.trans d₂.symm, s₁.trans s₂.symm, x₁.trans x₂.symm, c₁'.trans c₂'.symm,
        r₁.trans r₂.symm, by rw [rsp_ce, rsp_ce, rsp_two c₁ c₂]⟩)
    (fun _ => upd_sub) (fun _ => upd_wsub)
  -- `finalize`
  have f₁ : RelCT isa (Two fun _ _ => True) (.block pkFinalizeArgs) (Two FinArgs) :=
    two_blk [.rsp] rspOnly (by taint_decide) fun _ _ _ _ _ _ hc _ =>
      WP.mono (finArgs_ok hc) fun _ ⟨hc', _, ha⟩ => ⟨hc', ha⟩
  have f₂ := two_callP (n := Spec.Sha512.finalizeApi.name ++ v.suffix) (Φ := FinArgs)
    (fin_verified v).1 (fin_verified v).2.1 (fin_nosp v) (fin_depth v) (fun _ => finRd) finWr
    (fun _ _ _ _ _ hL hc ha => fin_pre hL hc ha)
    (fun L t₁ t₂ _ _ _ _ _ _ c₁ c₂ a₁ a₂ => by
      obtain ⟨d₁, s₁, x₁, c₁'⟩ := fin_regs a₁ finRd (finWr L)
      obtain ⟨d₂, s₂, x₂, c₂'⟩ := fin_regs a₂ finRd (finWr L)
      exact ⟨d₁.trans d₂.symm, s₁.trans s₂.symm, x₁.trans x₂.symm, c₁'.trans c₂'.symm,
        by rw [rsp_ce, rsp_ce, rsp_two c₁ c₂]⟩)
    (fun _ => fin_sub) (fun _ => fin_wsub)
  -- the scalar and the base point
  have b₁ : RelCT isa (Two fun _ _ => True) (.block pkBaseArgs) (Two BaseArgs) :=
    two_blk [.rsp] rspOnly (by taint_decide) fun _ _ _ _ _ _ hc _ =>
      WP.mono (baseArgs_ok hc) fun _ ⟨hc', _, ha⟩ => ⟨hc', ha⟩
  have b₂ : RelCT isa (Two BaseArgs) (.block pkPrune) (Two BaseArgs) := by
    refine two_blk [.rsp, .rdx] (fun L t₁ t₂ _ _ _ _ _ _ c₁ c₂ a₁ a₂ r hr => ?_) (by taint_decide)
      fun _ _ _ _ _ _ hc ha => WP.mono (prune_ok hc ha rfl) fun _ ⟨hc', _, ha', _⟩ => ⟨hc', ha'⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact rsp_two c₁ c₂
    · exact a₁.2.2.trans a₂.2.2.symm
  have b₃ := two_callP (n := scalarBaseName) (Φ := BaseArgs)
    Proof.Ed25519.X86_64.scalarBase_precomputed_ok Proof.Ed25519.X86_64.scalarBase_precomputed_ct
    base_nosp base_depth baseRd baseWr (fun _ _ _ _ _ hL hc ha => base_pre hL hc ha)
    (fun L t₁ t₂ _ _ _ _ _ _ c₁ c₂ a₁ a₂ => by
      obtain ⟨d₁, s₁, x₁⟩ := base_regs a₁ (baseRd L) (baseWr L)
      obtain ⟨d₂, s₂, x₂⟩ := base_regs a₂ (baseRd L) (baseWr L)
      exact ⟨by rw [rsp_ce, rsp_ce, rsp_two c₁ c₂], d₁.trans d₂.symm, s₁.trans s₂.symm, x₁.trans x₂.symm⟩)
    (fun _ => base_sub) (fun _ => base_wsub)
  have w : RelCT isa (Two fun _ _ => True) (.block pkWipe) fun _ _ => True :=
    two_block [.rsp] rspOnly (by taint_decide)
  exact ((i₁.seq i₂).seq ((u₁.seq u₂).seq (f₁.seq f₂))).seq (b₁.seq (b₂.seq (b₃.seq w)))

end VG.Proof.Ed25519.X86_64.PublicKey
