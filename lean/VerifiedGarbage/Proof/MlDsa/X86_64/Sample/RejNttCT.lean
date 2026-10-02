import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.RejNtt

/-!
# ML-DSA on x86-64: `vg_mldsa_rej_ntt_poly`, constant time but for the seed

Untrusted: everything here is checked by Lean. Two runs whose seeds (the
declared leak) and pointers agree leak the same: the prologue and the
blocks around the loop by the taint analysis, the sponge by `sponge_ct`,
and the loop, whose branches and stores depend on the XOF output, by
relating the two runs iteration by iteration (`body_ct`): both are at the
same iteration with the same coefficients sampled and the same bytes to
read, so each branch goes the same way and each store goes to the same
address.
-/

namespace VG.Proof.MlDsa.X86_64.Sample

open VG VG.X86_64
open VG.Proof.MlKem.X86_64
open VG.Impl.MlDsa.X86_64.Sample
open VG.Proof.MlDsa.Sample
open VG.Spec.MlDsa (Zq q G)
open VG.Spec.Sha3 (bytesAt)

/-- What holds of every run of `c` from `s` that `Q a` does, for any `a`
with `Pre a` (by determinism). -/
theorem WP.all' {c : Prog isa} {s : State} {α : Sort _} {Pre : α → Prop} {Q : α → State → Prop}
    (h : ∀ a, Pre a → WP isa c s (Q a)) (hne : ∃ a, Pre a) : WP isa c s fun s' => ∀ a, Pre a → Q a s' := by
  obtain ⟨a₀, h₀⟩ := hne
  obtain ⟨t, s', e, -⟩ := h a₀ h₀
  refine ⟨t, s', e, fun a ha => ?_⟩
  obtain ⟨t', s'', e', q⟩ := h a ha
  obtain ⟨-, rfl⟩ := Exec.det e e'
  exact q

theorem nil_regs {P : State → State → Prop} : ∀ x y, P x y → ∀ r ∈ ([] : List Reg), x.gpr r = y.gpr r :=
  fun _ _ _ _ h => absurd h List.not_mem_nil

namespace RejNttCT

/-! ## A try -/

theorem rnTry_all (s : State) (hne : ∃ aP L, TryPre s aP L) :
    WP isa rnTry s fun s' => ∀ aP L, TryPre s aP L →
      s'.gpr .rdi = BitVec.ofNat 64 (rnTryL L ((s.gpr .r8).setWidth 32).toNat).length ∧
      Stored s'.mem aP (rnTryL L ((s.gpr .r8).setWidth 32).toNat) ∧ Frame [pR aP] s.mem s'.mem ∧
      Keep [.rdi] s s' := by
  have := WP.all' (Pre := fun p : Addr × List Zq => TryPre s p.1 p.2)
    (Q := fun p s' => s'.gpr .rdi = BitVec.ofNat 64 (rnTryL p.2 ((s.gpr .r8).setWidth 32).toNat).length ∧
      Stored s'.mem p.1 (rnTryL p.2 ((s.gpr .r8).setWidth 32).toNat) ∧ Frame [pR p.1] s.mem s'.mem ∧
      Keep [.rdi] s s')
    (fun p h => rnTry_ok s h) (by obtain ⟨aP, L, h⟩ := hne; exact ⟨(aP, L), h⟩)
  exact WP.mono this fun s' h aP L hp => h (aP, L) hp

/-- The hypotheses of `rnMid_ok`. -/
structure MPre (s : State) (aP : Addr) (L : List Zq) : Prop where
  rbp : s.gpr .rbp = aP
  rdi : s.gpr .rdi = BitVec.ofNat 64 L.length
  len : L.length ≤ 256
  wr : CoeffsWr s.wr aP
  st : Stored s.mem aP L
  cf : s.cf = some (decide ((s.gpr .rdi).toNat < 256))

/-- After the loads. -/
def R1 (s₁ s₂ : State) : Prop :=
  ∃ aP L, MPre s₁ aP L ∧ MPre s₂ aP L ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .rcx = s₂.gpr .rcx ∧
    s₁.gpr .rsi = s₂.gpr .rsi

theorem traceTry {h1 : VG.Taint.Hint X86_64.Taint.T}
    (c1 : (taint.check (X86_64.Taint.ofRegs []) (.block [.alu32 .cmp .r8 (.imm qImm)]) h1).isSome = true)
    {h2 : VG.Taint.Hint X86_64.Taint.T}
    (c2 : (taint.check (X86_64.Taint.ofRegs [.rbp, .rdi]) (.block [.store32 aJ .r8, .alu .add .rdi (.imm 1)])
      h2).isSome = true)
    {h3 : VG.Taint.Hint X86_64.Taint.T} (c3 : (taint.check (X86_64.Taint.ofRegs []) (.block []) h3).isSome = true) :
    RelCT isa (fun s₁ s₂ => s₁.gpr .rbp = s₂.gpr .rbp ∧ s₁.gpr .rdi = s₂.gpr .rdi ∧
      (s₁.gpr .r8).setWidth 32 = (s₂.gpr .r8).setWidth 32) rnTry fun _ _ => True := by
  refine RelCT.seq (R := fun (s₁ s₂ : State) => s₁.cf = s₂.cf ∧ s₁.gpr .rbp = s₂.gpr .rbp ∧ s₁.gpr .rdi = s₂.gpr .rdi)
    (RelCT.postDep (F := fun (x x' : State) => x'.cf = some (decide (((x.gpr .r8).setWidth 32).toNat < q)) ∧
        x'.gpr = x.gpr)
      (taintRel [] nil_regs c1)
      (fun x y _ => ⟨WP.mono (rnCmp_ok x) fun _ h => ⟨h.1, h.2.2.1⟩,
        WP.mono (rnCmp_ok y) fun _ h => ⟨h.1, h.2.2.1⟩⟩)
      fun x y x' y' ⟨e1, e2, e3⟩ ⟨f1, g1⟩ ⟨f2, g2⟩ => ⟨by rw [f1, f2, e3], by rw [g1, g2, e1], by rw [g1, g2, e2]⟩) ?_
  exact RelCT.ite (fun x y h => h.1)
    (taintRel [.rbp, .rdi] (fun x y h r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      exacts [h.1.2.1, h.1.2.2]) c2)
    (taintRel [] nil_regs c3)

theorem ofNat64_toNat' {j : Nat} (h : j ≤ 256) : (BitVec.ofNat 64 j).toNat = j := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

theorem mid_ct : RelCT isa R1 (.ite .b rnTry (.block []))
    fun s₁ s₂ => s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .rsi = s₂.gpr .rsi := by
  refine RelCT.ite (fun x y ⟨aP, L, p1, p2, _⟩ => by
      show x.cf = y.cf; rw [p1.cf, p2.cf, p1.rdi, p2.rdi]) ?_ ?_
  · refine RelCT.postDep (F := fun (x x' : State) => ∀ aP L, TryPre x aP L →
        x'.gpr .rdi = BitVec.ofNat 64 (rnTryL L ((x.gpr .r8).setWidth 32).toNat).length ∧
        Stored x'.mem aP (rnTryL L ((x.gpr .r8).setWidth 32).toNat) ∧ Frame [pR aP] x.mem x'.mem ∧
        Keep [.rdi] x x')
      (RelCT.mono (traceTry (by taint_decide) (by taint_decide) (by taint_decide)) (fun x y h => by
        obtain ⟨⟨aP, L, p1, p2, e8, _, _⟩, _⟩ := h
        exact ⟨by rw [p1.rbp, p2.rbp], by rw [p1.rdi, p2.rdi], by rw [e8]⟩) fun _ _ h => h) ?_ ?_
    · intro x y ⟨⟨aP, L, p1, p2, _⟩, hb⟩
      have hl : L.length < 256 := by
        have : x.cf = some true := hb
        rw [p1.cf, p1.rdi, ofNat64_toNat' p1.len] at this; simpa using this
      exact ⟨rnTry_all x ⟨aP, L, p1.rbp, p1.rdi, hl, p1.wr, p1.st⟩,
        rnTry_all y ⟨aP, L, p2.rbp, p2.rdi, hl, p2.wr, p2.st⟩⟩
    · intro x y x' y' ⟨⟨aP, L, p1, p2, _, ecx, esi⟩, hb⟩ f1 f2
      have hl : L.length < 256 := by
        have : x.cf = some true := hb
        rw [p1.cf, p1.rdi, ofNat64_toNat' p1.len] at this; simpa using this
      obtain ⟨_, _, _, k1⟩ := f1 aP L ⟨p1.rbp, p1.rdi, hl, p1.wr, p1.st⟩
      obtain ⟨_, _, _, k2⟩ := f2 aP L ⟨p2.rbp, p2.rdi, hl, p2.wr, p2.st⟩
      exact ⟨by rw [k1.gpr (by decide), k2.gpr (by decide), ecx], by rw [k1.gpr (by decide), k2.gpr (by decide), esi]⟩
  · refine RelCT.postDep (F := fun (x x' : State) => x' = x) (taintRel [] nil_regs
      (by taint_decide)) (fun x y _ => ⟨WP.block_nil rfl, WP.block_nil rfl⟩) ?_
    intro x y x' y' ⟨⟨_, _, _, _, _, ecx, esi⟩, _⟩ f1 f2
    rw [f1, f2]; exact ⟨ecx, esi⟩

/-! ## An iteration -/

/-- The hypotheses of `rnBody_ok`. -/
structure BPre (s : State) (aP : Addr) (L : List Zq) : Prop where
  rbp : s.gpr .rbp = aP
  rdi : s.gpr .rdi = BitVec.ofNat 64 L.length
  len : L.length ≤ 256
  wr : CoeffsWr s.wr aP
  st : Stored s.mem aP L
  r0 : InRegions (s.rd ++ s.wr) (s.gpr .rsi) 1
  r1 : InRegions (s.rd ++ s.wr) (s.gpr .rsi + BitVec.ofNat 64 1) 1
  r2 : InRegions (s.rd ++ s.wr) (s.gpr .rsi + BitVec.ofNat 64 2) 1

/-- Two runs at the start of an iteration, with the same coefficients sampled
and the same bytes to read. -/
def BRel (s₁ s₂ : State) : Prop :=
  ∃ aP L, BPre s₁ aP L ∧ BPre s₂ aP L ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rcx = s₂.gpr .rcx ∧
    ∀ k < 3, s₁.mem (s₁.gpr .rsi + BitVec.ofNat 64 k) = s₂.mem (s₂.gpr .rsi + BitVec.ofNat 64 k)

theorem load_ct : RelCT isa BRel (.block rnLoad) R1 := by
  refine RelCT.postDep (F := fun (x x' : State) =>
      (x'.gpr .r8 = BitVec.setWidth 64 (rnw (x.mem (x.gpr .rsi)) (x.mem (x.gpr .rsi + BitVec.ofNat 64 1))
          (x.mem (x.gpr .rsi + BitVec.ofNat 64 2))) ∧
        x'.cf = some (decide ((x.gpr .rdi).toNat < 256)) ∧ x'.mem = x.mem ∧ x'.gpr .rdi = x.gpr .rdi) ∧
      Keep [.rax, .rdx, .r8, .rdi] x x')
    (taintRel [.rsi] (fun x y ⟨_, _, _, _, esi, _⟩ r hr => by simp at hr; subst hr; exact esi) (by taint_decide))
    (fun x y ⟨_, _, p1, p2, _⟩ => ⟨rnLoad_ok x p1.r0 p1.r1 p1.r2, rnLoad_ok y p2.r0 p2.r1 p2.r2⟩) ?_
  intro x y x' y' ⟨aP, L, p1, p2, esi, ecx, eb⟩ ⟨⟨h8, hc, hm, hdi⟩, k⟩ ⟨⟨h8', hc', hm', hdi'⟩, k'⟩
  have e0 := eb 0 (by decide)
  rw [add_ofNat_zero, add_ofNat_zero] at e0
  have mp : ∀ {s s' : State}, BPre s aP L → s'.cf = some (decide ((s.gpr .rdi).toNat < 256)) →
      s'.mem = s.mem → s'.gpr .rdi = s.gpr .rdi → Keep [.rax, .rdx, .r8, .rdi] s s' → MPre s' aP L :=
    fun {s s'} p c m d kk => ⟨by rw [kk.gpr (by decide), p.rbp], by rw [d, p.rdi], p.len, by rw [kk.2.2]; exact p.wr,
      by rw [m]; exact p.st, by rw [c, d]⟩
  exact ⟨aP, L, mp p1 hc hm hdi k, mp p2 hc' hm' hdi' k',
    by rw [h8, h8', e0, eb 1 (by decide), eb 2 (by decide)], by rw [k.gpr (by decide), k'.gpr (by decide), ecx],
    by rw [k.gpr (by decide), k'.gpr (by decide), esi]⟩

theorem step_ct : RelCT isa (fun s₁ s₂ => s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .rsi = s₂.gpr .rsi)
    (.block [.alu .add .rsi (.imm 3), .alu .sub .rcx (.imm 1)]) fun s₁ s₂ => s₁.zf = s₂.zf :=
  RelCT.postDep (F := fun (x x' : State) => x'.zf = some (x.gpr .rcx - 1 == 0))
    (taintRel [] nil_regs (by taint_decide))
    (fun x y _ => ⟨WP.mono (step_ok x 3) fun _ h => h.1.2.2.1, WP.mono (step_ok y 3) fun _ h => h.1.2.2.1⟩)
    fun x y x' y' e f1 f2 => by rw [f1, f2, e.1]

theorem body_ct : RelCT isa BRel rnBody fun s₁ s₂ => s₁.zf = s₂.zf :=
  RelCT.seq load_ct (RelCT.seq mid_ct step_ct)

end RejNttCT

/-! ## The whole function -/

namespace RejNtt

open RejNttCT

section
variable {σ₁ σ₂ : State} (hq : rnK.pub σ₁ σ₂)
include hq

theorem pub_X : X σ₁ = X σ₂ := by simp only [X, B, hq.2.2.2.2]
theorem pub_sp : spOf σ₁ = spOf σ₂ := by simp only [spOf, hq.1, hq.2.1, hq.2.2.1]
theorem pub_aP : σ₁.gpr .rsi = σ₂.gpr .rsi := hq.2.1
theorem pub_Lt (t : Nat) : Lt σ₁ t = Lt σ₂ t := by simp only [Lt, pub_X hq]

theorem spPub : SpPub (spOf σ₁) (spOf σ₂) σ₁ σ₂ :=
  ⟨hq.1, rfl, hq.2.2.1, hq.2.1, rfl, hq.2.2.2.1⟩

end

/-- Two runs at iteration `t`, `n = 336 - t` iterations from the end. -/
def LI (n : Nat) (s₁ s₂ : State) : Prop :=
  ∃ σ₁ σ₂ t, rnK.pre σ₁ ∧ rnK.pre σ₂ ∧ rnK.pub σ₁ σ₂ ∧ n = 336 - t ∧ t < 336 ∧ LAt σ₁ t s₁ ∧ LAt σ₂ t s₂

theorem bpre {σ : State} (hp : rnK.pre σ) {t : Nat} (ht : t < 336) {s : State} (h : LAt σ t s) :
    BPre s (σ.gpr .rsi) (Lt σ t) :=
  ⟨h.env.rbp, h.rdi, Lt_length_le t, .of_mem (by rw [h.env.wr, hp.2.1]; simp), h.stored,
    by simpa using lat_regions hp h (k := 0) (by omega), lat_regions hp h (by omega), lat_regions hp h (by omega)⟩

theorem li_brel {n : Nat} {s₁ s₂ : State} (h : LI n s₁ s₂) : BRel s₁ s₂ := by
  obtain ⟨σ₁, σ₂, t, p₁, p₂, hq, _, ht, l₁, l₂⟩ := h
  refine ⟨σ₁.gpr .rsi, Lt σ₁ t, bpre p₁ ht l₁, by rw [pub_aP hq, pub_Lt hq]; exact bpre p₂ ht l₂,
    by rw [l₁.rsi, l₂.rsi, pub_sp hq], by rw [l₁.rcx, l₂.rcx], fun k hk => ?_⟩
  rw [out_byte l₁ (by omega), out_byte l₂ (by omega), pub_X hq]

theorem loop_ct (n : Nat) :
    RelCT isa (LI n) (.loop rnBody .ne) (Rel2 rnK.pre rnK.pub fun σ s => LAt σ 336 s) := by
  refine RelCT.loop (M := isa) LI (fun n => ?_) n
  refine RelCT.postDep (F := fun (x x' : State) => ∀ p : State × Nat, rnK.pre p.1 ∧ p.2 < 336 ∧ LAt p.1 p.2 x →
      LAt p.1 (p.2 + 1) x' ∧ x'.zf = some (BitVec.ofNat 64 (336 - p.2) - 1 == 0))
    (RelCT.mono body_ct (fun x y h => li_brel h) fun _ _ _ => trivial) (fun x y h => ?_) ?_
  · obtain ⟨σ₁, σ₂, t, p₁, p₂, _, _, ht, l₁, l₂⟩ := h
    exact ⟨WP.all' (fun p hp' => lat_step hp'.1 hp'.2.1 hp'.2.2) ⟨(σ₁, t), p₁, ht, l₁⟩,
      WP.all' (fun p hp' => lat_step hp'.1 hp'.2.1 hp'.2.2) ⟨(σ₂, t), p₂, ht, l₂⟩⟩
  · intro x y x' y' ⟨σ₁, σ₂, t, p₁, p₂, hq, hn, ht, l₁, l₂⟩ f₁ f₂
    obtain ⟨l₁', z₁⟩ := f₁ (σ₁, t) ⟨p₁, ht, l₁⟩
    obtain ⟨l₂', z₂⟩ := f₂ (σ₂, t) ⟨p₂, ht, l₂⟩
    have ez : (BitVec.ofNat 64 (336 - t) - 1 == 0) = decide (t + 1 = 336) := by
      rw [ofNat64_pred (by omega) (by omega), ofNat64_beq_zero (by omega)]
      exact decide_eq_decide.mpr (by omega)
    rw [ez] at z₁ z₂
    refine ⟨by show x'.zf.map _ = y'.zf.map _; rw [z₁, z₂], fun hf => ?_, fun ht' => ?_⟩
    · have : t + 1 = 336 := by
        have : x'.zf.map (!·) = some false := hf
        rw [z₁] at this; simpa using this
      rw [this] at l₁' l₂'
      exact ⟨σ₁, σ₂, p₁, p₂, hq, l₁', l₂'⟩
    · have : t + 1 ≠ 336 := by
        have : x'.zf.map (!·) = some true := ht'
        rw [z₁] at this; simpa using this
      exact ⟨336 - (t + 1), by omega, σ₁, σ₂, t + 1, p₁, p₂, hq, rfl, by omega, l₁', l₂'⟩

/-- After the first block of the loop's setup. -/
def IA (σ s : State) : Prop :=
  Env (spOf σ) σ s ∧ bytesAt s.mem ((spOf σ).at' 840) 1008 = X σ ∧ s.gpr .rsi = (spOf σ).at' 840 ∧
    s.gpr .rdi = 0

theorem latB {σ s : State} (h : IA σ s) : WP isa (.block [.mov32 .rcx (.imm 336)]) s (LAt σ 0) := by
  refine WP.mono (WP.keep [.rcx] (Q := fun s' => s'.mem = s.mem ∧ s'.gpr .rcx = BitVec.ofNat 64 336)
    (by xrun) (by decide)) fun s2 ⟨⟨hm2, hcx⟩, k2⟩ => ?_
  exact ⟨h.1.keep hm2 (k2.mono (by decide)), by rw [hm2]; exact h.2.1, by rw [k2.gpr (by decide), h.2.2.1]; simp,
    by rw [k2.gpr (by decide), h.2.2.2]; rfl, hcx, by rw [hm2]; exact stored_nil _ _⟩

theorem hok : ∀ σ, rnK.pre σ → SpOk (spOf σ) σ := fun _ hp => spOk hp

theorem hpub : ∀ σ₁ σ₂, rnK.pre σ₁ → rnK.pre σ₂ → rnK.pub σ₁ σ₂ → SpPub (spOf σ₁) (spOf σ₂) σ₁ σ₂ :=
  fun _ _ _ _ hq => spPub hq

/-- The loop and the end. -/
theorem tail_ct : RelCT isa (Rel2 rnK.pre rnK.pub fun σ => J6 168 1008 (spOf σ) σ)
    (.seq rnLoop (.block (retJ ++ epi))) fun _ _ => True := by
  refine RelCT.seq (RelCT.seq (relInv (I' := IA) (fun σ s _ h => lat0 h)
      (taintSp hpub (fun _ _ h => h.env) [] nil_regs (by taint_decide)))
    (RelCT.seq (RelCT.mono (relInv (I' := fun σ s => LAt σ 0 s) (fun σ s _ h => latB h)
        (taintSp hpub (J := fun P σ s => Env P σ s ∧ bytesAt s.mem ((spOf σ).at' 840) 1008 = X σ ∧
          s.gpr .rsi = (spOf σ).at' 840 ∧ s.gpr .rdi = 0) (fun _ _ h => h.1) [] nil_regs (by taint_decide)))
      (fun _ _ h => h) fun _ _ ⟨σ₁, σ₂, p₁, p₂, hq, l₁, l₂⟩ => ⟨σ₁, σ₂, 0, p₁, p₂, hq, rfl, by omega, l₁, l₂⟩)
      (loop_ct 336))) ?_
  exact taintSp hpub (J := fun P σ s => LAt σ 336 s) (fun _ _ h => h.env) [] nil_regs (by taint_decide)

end RejNtt

open RejNtt RejNttCT in
theorem rejNTT_ct : ConstantTime isa rnK.pre rnK.pub Impl.MlDsa.X86_64.Sample.rejNTT := by
  refine relStart (Q := fun _ _ => True) (RelCT.seq (relInv (I' := fun σ => J0 (spOf σ) σ)
    (fun σ s hp h => by subst h; exact pro_ok hp)
    (taintRel [.rdi, .rsi, .rdx, .rsp] (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ r hr => by
      subst h₁ h₂
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      exacts [hq.1, hq.2.1, hq.2.2.1, hq.2.2.2.1]) (by taint_decide))) ?_)
  exact RelCT.seq (sponge_ct hok hpub (.inr rfl) (by decide) (by taint_decide) (by taint_decide) (by taint_decide))
    tail_ct

end VG.Proof.MlDsa.X86_64.Sample

namespace VG.Proof.MlDsa.X86_64.Sample

open VG VG.X86_64
open VG.Proof.MlDsa.Sample
open VG.Spec.MlDsa (G)
open VG.Spec.Sha3 (bytesAt)

theorem leakBytes_inj : ∀ {a b : List Byte}, a.map (fun x => x.toNat) = b.map (fun x => x.toNat) → a = b
  | [], [], _ => rfl
  | x :: a, y :: b, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [BitVec.eq_of_toNat_eq h.1, leakBytes_inj h.2]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

/-- A state satisfying the precondition. -/
def rnSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x3000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 34⟩]
  wr := [⟨0x2000, 1024⟩, ⟨0x3000, 2048⟩]

theorem rejNTT_verified :
    Verified X86_64.target Impl.MlDsa.X86_64.Sample.rejNTT (Spec.MlDsa.rejNTTContract X86_64.abi 16) :=
  Verified.of_correct rejNTT_correct rejNTT_ct
    { pre := by sig_implies_pre [Spec.MlDsa.rejNTTContract, Spec.MlDsa.rejNTTSig, rnK, X86_64.abi,
        X86_64.argRegs]
      post := by
        intro s s' _ h
        sig_post [Spec.MlDsa.rejNTTContract, Spec.MlDsa.rejNTTSig, rnK, X86_64.abi, X86_64.argRegs]
        dsimp only [rnK] at h
        obtain ⟨hr, hp⟩ := h
        by_cases hf : (rnFold [] (G (bytesAt s.mem (s.gpr .rdi) 34) 1008)).length = 256
        · rw [ifT hf] at hr
          obtain ⟨hred, hpoly⟩ := hp hf
          exact ⟨fun _ => hred, .inl ⟨hr, { Spec.MlDsa.minBounds with rejNTT := 1008 }, by
            show Spec.MlDsa.rejNTTPoly 1008 _ = _
            rw [rejNTT_some hf, hpoly]⟩⟩
        · rw [ifF hf] at hr
          exact ⟨fun h1 => absurd (hr.symm.trans h1) (by decide),
            .inr ⟨hr, rejNTT_none (B := 1008) (by decide) (by decide) hf⟩⟩
      pub := by
        intro s₁ s₂ _ _ h
        sig_pub [Spec.MlDsa.rejNTTContract, Spec.MlDsa.rejNTTSig, rnK, X86_64.abi, X86_64.argRegs] at h
        obtain ⟨hsp, hb, hdi, hsi, hdx⟩ := h
        exact ⟨hdi, hsi, hdx, hsp, leakBytes_inj hb⟩
      sat := by sig_implies_sat [Spec.MlDsa.rejNTTContract, Spec.MlDsa.rejNTTSig, rnK, X86_64.abi,
        X86_64.argRegs] [rnSat] using rnSat }

end VG.Proof.MlDsa.X86_64.Sample
