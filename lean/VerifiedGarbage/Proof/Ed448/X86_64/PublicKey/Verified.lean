import VerifiedGarbage.Proof.Ed448.X86_64.PublicKey.Base
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.Contract

/-!
# Ed448 public-key derivation on x86-64: `Verified`

The frame's body leaves the public key in `out` (`body_ok`), and the whole
function meets `pkLocal` and the ABI (`publicKey_ok`).

Constant time: two runs whose pointers agree have the same layout, so between
the frame's push and pop they are related by `Two`: both satisfy `Ctx` with
that layout (and `Φ`, what the next block or call needs of the registers),
whatever their secrets. The blocks address only the stack and `scratch`, from
registers that agree (the taint analysis); each call is of constant-time code
whose public data, its pointers and lengths, agree (`RelCT.callEx`).
-/

namespace VG.Proof.Ed448.X86_64.PublicKey

open VG VG.X86_64 VG.Impl.Ed448.X86_64

variable {L : Lay} {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem}

/-! ## Correctness -/

/-- The public key of the seed in `out`. -/
theorem body_ok (hL : L.Ok) {t : State} (hc : Ctx L g mx m₀ t) :
    WP isa pkBody t fun t' => Ctx L g mx m₀ t' ∧
      Spec.Ed448.bytesAt t'.mem L.out 57 = Spec.Ed448.publicKey (Spec.Ed448.bytesAt m₀ L.seed 57) := by
  refine WP.seq (WP.mono (hash_ok hL hc) fun t₁ ⟨hc₁, hh₁⟩ => ?_)
  refine WP.seq (WP.mono (prune_ok hc₁ hh₁) fun t₂ ⟨hc₂, hs₂⟩ => ?_)
  refine WP.seq (WP.mono (baseArgs_ok hc₂) fun t₃ ⟨hc₃, hm₃, ha₃⟩ => ?_)
  refine WP.seq (WP.mono (base_ok hL hc₃ ha₃ (hm₃ ▸ hs₂)) fun t₄ ⟨hc₄, ho₄⟩ => ?_)
  refine WP.mono (wipe_ok hc₄) fun t₅ ⟨hc₅, hf₅⟩ => ⟨hc₅, ?_⟩
  have e : Spec.Ed448.bytesAt t₅.mem L.out 57 = Spec.Ed448.bytesAt t₄.mem L.out 57 := by
    simp only [Spec.Ed448.bytesAt]
    refine List.map_congr_left fun i hi => ?_
    exact Frame.bytes (R := L.OUT) hf₅ (by
      intro r hr; simp only [List.mem_singleton] at hr; subst hr
      exact (hL.stk_OUT (d := 16) (n := 64) (by omega)).symm) (by show (57 : Nat) ≤ 2 ^ 64; decide)
      (List.mem_range.mp hi)
  rw [e, ho₄]
  rfl

theorem pop_rsp (B : Addr) : B + BitVec.ofNat 64 16 + BitVec.ofNat 64 (8 * 11) = B + BitVec.ofNat 64 104 := by
  rw [add_add]

/-- `vg_ed448_public_key` meets `pkLocal` and the ABI. -/
theorem publicKey_ok {s : State} (h : pkLocal.pre s) :
    WP isa publicKey s fun s' => abiPreserved s s' ∧ pkLocal.post s s' := by
  have hL := lay_ok h
  have hc := push_ctx h
  refine WP.frame (rs := pushRs) (by decide) (by decide) (by decide) (by show 8 * 11 ≤ _; have := h.1; omega)
    (WP.mono (body_ok hL hc) fun u ⟨hu, ho⟩ => ⟨hu.rsp.trans hc.rsp.symm, hu.wr.trans hc.wr.symm, ?_, ?_⟩)
  · have hrsp : (popped .rax pushRs.length u).gpr .rsp = s.gpr .rsp := by
      rw [popped_rsp, hu.rsp, show pushRs.length = 11 from rfl, pop_rsp, lay_ret]
    refine ⟨fun r hr => ?_, ?_, by rw [popped_mxcsr, hu.mx]⟩
    · by_cases hr' : r = .rsp
      · subst hr'; exact hrsp
      · rw [popped_gpr _ _ _ hr' (ne_cs hr (by decide)), hu.cs r hr hr']
    · rw [popped_mem]
      refine hu.frame.readW (r := (lay s).RET) ?_ ?_ (by decide)
      · rw [Lay.RET, lay_ret]; exact Region.contains_self _ _
      · intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact hL.ro
        · exact hL.rc
        · exact Offset.disjoint_base _ (by omega) (by omega)
  · show Spec.Ed448.bytesAt (popped .rax pushRs.length u).mem (lay s).out 57 = _
    rw [popped_mem, ho]
    rfl

/-! ## Constant time -/

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

theorem covers {t : State} (hc : Ctx L g mx m₀ t) {rd wr : List Region}
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

/-- `rsp` and the register `r`, which `Φ` fixes for the layout. -/
theorem rspAnd {Φ : Lay → State → Prop} (r : Reg) (v : Lay → BitVec 64) (hv : ∀ L t, Φ L t → t.gpr r = v L) :
    ∀ (L : Lay) (t₁ t₂ : State) g₁ g₂ mx₁ mx₂ m₁ m₂,
    Ctx L g₁ mx₁ m₁ t₁ → Ctx L g₂ mx₂ m₂ t₂ → Φ L t₁ → Φ L t₂ → ∀ x ∈ [Reg.rsp, r], t₁.gpr x = t₂.gpr x := by
  intro L t₁ t₂ _ _ _ _ _ _ c₁ c₂ f₁ f₂ x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · exact rsp_two c₁ c₂
  · exact (hv L t₁ f₁).trans (hv L t₂ f₂).symm

/-- The frame's body. -/
theorem body_ct : RelCT isa (Two fun _ _ => True) pkBody fun _ _ => True := by
  -- zeroing the state
  have z₁ : RelCT isa (Two fun _ _ => True) (.block pkZeroHead)
      (Two fun L t => t.gpr .rdi = L.scr ∧ t.gpr .rax = 0) :=
    two_blk [.rsp] rspOnly (by taint_decide) fun _ _ _ _ _ _ hc _ =>
      WP.mono (zeroHead_ok hc) fun _ ⟨hc', _, h1, h2⟩ => ⟨hc', h1, h2⟩
  have z₂ : RelCT isa (Two fun L t => t.gpr .rdi = L.scr ∧ t.gpr .rax = 0) (.block pkZeroStores)
      (Two fun _ _ => True) :=
    two_wp (two_block [.rsp, .rdi] (rspAnd .rdi Lay.scr fun _ _ h => h.1) (by taint_decide))
      fun _ _ _ _ t hL hc hf => WP.mono (zstores_ok hL 25 (by omega) t hc hf.1 hf.2) fun _ h => ⟨h.1, trivial⟩
  -- `absorb`
  have a₁ : RelCT isa (Two fun _ _ => True) (.block pkAbsorbArgs) (Two AbsArgs) :=
    two_blk [.rsp] rspOnly (by taint_decide) fun _ _ _ _ _ _ hc _ =>
      WP.mono (absArgs_ok hc) fun _ ⟨hc', _, ha⟩ => ⟨hc', ha⟩
  have a₂ := two_callP (n := "vg_keccak_absorb") (Φ := AbsArgs)
    Proof.Sha3.X86_64.Stream.Absorb.absorb_correct Proof.Sha3.X86_64.Stream.Absorb.absorb_ct
    absorb_nosp absorb_depth absRd absWr (fun _ _ _ _ _ hL hc ha => abs_pre hL hc ha)
    (fun L t₁ t₂ _ _ _ _ _ _ c₁ c₂ a₁ a₂ => by
      obtain ⟨d₁, s₁, x₁, c₁', r₁, n₁⟩ := abs_regs a₁ (absRd L) (absWr L)
      obtain ⟨d₂, s₂, x₂, c₂', r₂, n₂⟩ := abs_regs a₂ (absRd L) (absWr L)
      exact ⟨d₁.trans d₂.symm, s₁.trans s₂.symm, x₁.trans x₂.symm, c₁'.trans c₂'.symm,
        r₁.trans r₂.symm, n₁.trans n₂.symm, by rw [rsp_ce, rsp_ce, rsp_two c₁ c₂]⟩)
    (fun _ => abs_sub) (fun _ => abs_wsub)
  -- `pad`
  have p₁ : RelCT isa (Two fun _ _ => True) (.block pkPadArgs) (Two PadArgs) :=
    two_blk [.rsp] rspOnly (by taint_decide) fun _ _ _ _ _ _ hc _ =>
      WP.mono (padArgs_ok hc) fun _ ⟨hc', _, ha⟩ => ⟨hc', ha⟩
  have p₂ := two_callP (n := "vg_keccak_pad") (Φ := PadArgs)
    Proof.Sha3.X86_64.Stream.Pad.pad_correct Proof.Sha3.X86_64.Stream.Pad.pad_ct
    pad_nosp pad_depth (fun _ => padRd) padWr (fun _ _ _ _ _ hL hc ha => pad_pre hL hc ha)
    (fun L t₁ t₂ _ _ _ _ _ _ c₁ c₂ a₁ a₂ => by
      obtain ⟨d₁, s₁, x₁, -, r₁⟩ := pad_regs a₁ padRd (padWr L)
      obtain ⟨d₂, s₂, x₂, -, r₂⟩ := pad_regs a₂ padRd (padWr L)
      exact ⟨d₁.trans d₂.symm, s₁.trans s₂.symm, x₁.trans x₂.symm, r₁.trans r₂.symm,
        by rw [rsp_ce, rsp_ce, rsp_two c₁ c₂]⟩)
    (fun _ => pad_sub) (fun _ => pad_wsub)
  -- `squeeze`
  have q₁ : RelCT isa (Two fun _ _ => True) (.block pkSqueezeArgs) (Two SqzArgs) :=
    two_blk [.rsp] rspOnly (by taint_decide) fun _ _ _ _ _ _ hc _ =>
      WP.mono (sqzArgs_ok hc) fun _ ⟨hc', _, ha⟩ => ⟨hc', ha⟩
  have q₂ := two_callP (n := "vg_keccak_squeeze") (Φ := SqzArgs)
    Proof.Sha3.X86_64.Stream.Squeeze.squeeze_correct Proof.Sha3.X86_64.Stream.Squeeze.squeeze_ct
    squeeze_nosp squeeze_depth (fun _ => sqzRd) sqzWr (fun _ _ _ _ _ hL hc ha => sqz_pre hL hc ha)
    (fun L t₁ t₂ _ _ _ _ _ _ c₁ c₂ a₁ a₂ => by
      obtain ⟨d₁, s₁, x₁, c₁', r₁, n₁⟩ := sqz_regs a₁ sqzRd (sqzWr L)
      obtain ⟨d₂, s₂, x₂, c₂', r₂, n₂⟩ := sqz_regs a₂ sqzRd (sqzWr L)
      exact ⟨d₁.trans d₂.symm, s₁.trans s₂.symm, x₁.trans x₂.symm, c₁'.trans c₂'.symm,
        r₁.trans r₂.symm, n₁.trans n₂.symm, by rw [rsp_ce, rsp_ce, rsp_two c₁ c₂]⟩)
    (fun _ => sqz_sub) (fun _ => sqz_wsub)
  -- pruning
  have r₁ : RelCT isa (Two fun _ _ => True) (.block [Instr.mov .rdx (.mem (stk fScratch))])
      (Two fun L t => t.gpr .rdx = L.scr) :=
    two_blk [.rsp] rspOnly (by taint_decide) fun _ _ _ _ _ _ hc _ =>
      WP.mono (rdx_ok hc) fun _ ⟨hc', _, h⟩ => ⟨hc', h⟩
  have r₂ : RelCT isa (Two fun L t => t.gpr .rdx = L.scr) (.block (pkLoads ++ (pkMods ++ pkStores)))
      (Two fun _ _ => True) :=
    two_wp (two_block [.rsp, .rdx] (rspAnd .rdx Lay.scr fun _ _ h => h) (by taint_decide))
      fun _ _ _ _ _ _ hc hd => WP.mono (pruneRest_ok hc hd rfl) fun _ h => ⟨h.1, trivial⟩
  -- the base point
  have b₁ : RelCT isa (Two fun _ _ => True) (.block pkBaseArgs) (Two BaseArgs) :=
    two_blk [.rsp] rspOnly (by taint_decide) fun _ _ _ _ _ _ hc _ =>
      WP.mono (baseArgs_ok hc) fun _ ⟨hc', _, ha⟩ => ⟨hc', ha⟩
  have b₂ := two_callP (n := "vg_ed448_scalar_base") (Φ := BaseArgs)
    Proof.Ed448.X86_64.scalarBase_ok Proof.Ed448.X86_64.scalarBase_ct
    base_nosp base_depth baseRd baseWr (fun _ _ _ _ _ hL hc ha => base_pre hL hc ha)
    (fun L t₁ t₂ _ _ _ _ _ _ c₁ c₂ a₁ a₂ => by
      obtain ⟨d₁, s₁, x₁⟩ := base_regs a₁ (baseRd L) (baseWr L)
      obtain ⟨d₂, s₂, x₂⟩ := base_regs a₂ (baseRd L) (baseWr L)
      exact ⟨by rw [rsp_ce, rsp_ce, rsp_two c₁ c₂], d₁.trans d₂.symm, s₁.trans s₂.symm, x₁.trans x₂.symm⟩)
    (fun _ => base_sub) (fun _ => base_wsub)
  have w : RelCT isa (Two fun _ _ => True) (.block pkWipe) fun _ _ => True :=
    two_block [.rsp] rspOnly (by taint_decide)
  exact ((z₁.seq z₂).seq ((a₁.seq a₂).seq ((p₁.seq p₂).seq (q₁.seq q₂)))).seq
    ((r₁.seq r₂).seq (b₁.seq (b₂.seq w)))

theorem publicKey_ct : ConstantTime isa pkLocal.pre pkLocal.pub publicKey := by
  refine RelCT.constantTime (RelCT.frame (fun _ _ h => h.2.2.1) (RelCT.mono body_ct ?_ fun _ _ _ => trivial))
  rintro _ _ ⟨s₁, s₂, ⟨h₁, h₂, hsp, hdi, hsi, hdx⟩, rfl, rfl⟩
  have e : lay s₂ = lay s₁ := by simp only [lay, hsp, hdi, hsi, hdx]
  exact ⟨⟨lay s₁, s₁.gpr, s₂.gpr, s₁.mxcsr, s₂.mxcsr, s₁.mem, s₂.mem⟩, lay_ok h₁, push_ctx h₁,
    e ▸ push_ctx h₂, trivial, trivial⟩

/-! ## The shared contract -/

theorem implies : pkLocal.Implies (Spec.Ed448.publicKeyContract X86_64.abi 104) := by
  sig_implies [Spec.Ed448.publicKeyContract, Spec.Ed448.publicKeySig, Spec.Ed448.scratchWords,
    X86_64.abi, X86_64.argRegs, pkLocal] [Proof.Ed448.X86_64.scalarBaseSat]
    using Proof.Ed448.X86_64.scalarBaseSat

theorem publicKey_verified :
    Verified X86_64.target publicKey (Spec.Ed448.publicKeyContract X86_64.abi 104) :=
  Verified.of_correct (fun _ h => publicKey_ok h) publicKey_ct implies

end VG.Proof.Ed448.X86_64.PublicKey
