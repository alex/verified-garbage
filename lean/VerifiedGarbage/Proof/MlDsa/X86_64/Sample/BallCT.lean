import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.Ball
import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.RejNttCT

/-!
# ML-DSA on x86-64: `vg_mldsa_sample_in_ball`, constant time but for `c̃`

Untrusted: everything here is checked by Lean. Two runs whose `c̃` (the
declared leak), `len`, `τ` and pointers agree leak the same: the prologue and
the blocks around the loop by the taint analysis, the sponge by
`sponge_ct`, and the loop, whose branches and addresses depend on the
SHAKE256 output, by relating the two runs iteration by iteration
(`body_ct`): both are at the same iteration with the same `i`, sign bits
and byte to read, so each branch goes the same way and each access goes to
the same address.
-/

namespace VG.Proof.MlDsa.X86_64.Sample

open VG VG.X86_64
open VG.Proof.MlKem.X86_64
open VG.Impl.MlDsa.X86_64.Sample
open VG.Proof.MlDsa.Sample
open VG.Spec.MlDsa (H)
open VG.Spec.Sha3 (bytesAt)
open VG.Impl.MlKem.X86_64 (at_)

/-- Code that writes only the registers `rs` keeps the others, in both runs. -/
theorem RelCT.keeps {c : Prog isa} (rs : List Reg) (hc : writesOnly rs c = true) {P Q : State → State → Prop}
    (h : RelCT isa P c fun _ _ => True)
    (hQ : ∀ x y x' y', P x y → (∀ r, r ∉ rs → x'.gpr r = x.gpr r) → (∀ r, r ∉ rs → y'.gpr r = y.gpr r) →
      Q x' y') : RelCT isa P c Q := by
  intro x y t₁ t₂ x' y' hp e₁ e₂
  refine ⟨(h _ _ _ _ _ _ hp e₁ e₂).1, hQ x y x' y' hp (fun r hr => Exec.gpr (fun i hi => ?_) e₁)
    (fun r hr => Exec.gpr (fun i hi => ?_) e₂)⟩ <;>
  · unfold writesOnly at hc
    rw [Code.allInstrs_eq, List.all_eq_true] at hc
    have := List.all_eq_true.mp (hc i hi) r (mem_allRegs r)
    simp only [Bool.or_eq_true, List.contains_iff_mem, hr, false_or, Bool.not_eq_true'] at this
    exact this

namespace BallCT

/-- Registers that agree in two runs. -/
def Same (rs : List Reg) (s₁ s₂ : State) : Prop := ∀ r ∈ rs, s₁.gpr r = s₂.gpr r

/-- Two runs at the start of an iteration: the same registers of the loop,
and the same byte to read. -/
def BRel (s₁ s₂ : State) : Prop :=
  Same [.rbp, .rdi, .rsi, .rcx, .r9] s₁ s₂ ∧ s₁.mem (s₁.gpr .rsi) = s₂.mem (s₂.gpr .rsi) ∧
    InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .rsi) 1 ∧ InRegions (s₂.rd ++ s₂.wr) (s₂.gpr .rsi) 1

/-- After the comparison of `i` with 256. -/
def R1 (s₁ s₂ : State) : Prop := BRel s₁ s₂ ∧ s₁.cf = s₂.cf

/-- After the load of the byte. -/
def R2 (s₁ s₂ : State) : Prop := Same [.rbp, .rdi, .rax, .r9, .rsi, .rcx] s₁ s₂ ∧ s₁.cf = s₂.cf

/-- The end of a try. -/
def RQ (s₁ s₂ : State) : Prop := Same [.rsi, .rcx] s₁ s₂

theorem same_of {rs : List Reg} {s₁ s₂ : State} (h : Same rs s₁ s₂) {r : Reg} (hr : r ∈ rs) :
    s₁.gpr r = s₂.gpr r := h r hr

theorem cmp_ct : RelCT isa BRel (.block [.alu .cmp .rdi (.imm 256)]) R1 :=
  RelCT.postDep (F := fun (x x' : State) => x'.cf = some (decide ((x.gpr .rdi).toNat < 256)) ∧ x'.mem = x.mem ∧
      x'.gpr = x.gpr ∧ x'.rd = x.rd ∧ x'.wr = x.wr)
    (taintRel [] nil_regs (by taint_decide)) (fun x y _ => ⟨cmpRdi_ok x, cmpRdi_ok y⟩)
    fun x y x' y' ⟨hs, hb, i₁, i₂⟩ ⟨c₁, m₁, g₁, r₁, w₁⟩ ⟨c₂, m₂, g₂, r₂, w₂⟩ =>
      ⟨⟨fun r hr => by rw [g₁, g₂]; exact hs r hr, by rw [m₁, m₂, g₁, g₂]; exact hb,
        by rw [r₁, w₁, g₁]; exact i₁, by rw [r₂, w₂, g₂]; exact i₂⟩,
        by rw [c₁, c₂, same_of hs (by decide : Reg.rdi ∈ _)]⟩

theorem load_ct : RelCT isa (fun s₁ s₂ => R1 s₁ s₂ ∧ isa.eval .b s₁ = some true)
    (.block [.movzx8 .rax (at_ .rsi 0), .alu .cmp .rdi (.reg .rax)]) R2 :=
  RelCT.postDep (F := fun (x x' : State) =>
      (x'.gpr .rax = BitVec.ofNat 64 (x.mem (x.gpr .rsi)).toNat ∧
        x'.cf = some (decide ((x.gpr .rdi).toNat < (x.mem (x.gpr .rsi)).toNat)) ∧ x'.mem = x.mem ∧
        x'.gpr .rdi = x.gpr .rdi) ∧ Keep [.rax, .rdi] x x')
    (taintRel [.rsi] (fun x y ⟨⟨⟨hs, _⟩, _⟩, _⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact same_of hs (by decide)) (by taint_decide))
    (fun x y ⟨⟨⟨_, _, i₁, i₂⟩, _⟩, _⟩ => ⟨bLoad_ok x i₁, bLoad_ok y i₂⟩)
    fun x y x' y' ⟨⟨⟨hs, hb, _⟩, _⟩, _⟩ ⟨⟨a₁, c₁, _, d₁⟩, k₁⟩ ⟨⟨a₂, c₂, _, d₂⟩, k₂⟩ => by
      refine ⟨fun r hr => ?_, by rw [c₁, c₂, hb, same_of hs (by decide : Reg.rdi ∈ _)]⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
      · rw [k₁.gpr (by decide), k₂.gpr (by decide)]; exact same_of hs (by decide)
      · rw [d₁, d₂]; exact same_of hs (by decide)
      · rw [a₁, a₂, hb]
      all_goals rw [k₁.gpr (by decide), k₂.gpr (by decide)]; exact same_of hs (by decide)

theorem nil_ct {P : State → State → Prop} (hP : ∀ x y, P x y → RQ x y) : RelCT isa P (.block []) RQ :=
  RelCT.postDep (F := fun (x x' : State) => x' = x) (taintRel [] nil_regs (by taint_decide))
    (fun x y _ => ⟨WP.block_nil rfl, WP.block_nil rfl⟩) fun x y x' y' h f₁ f₂ => by rw [f₁, f₂]; exact hP x y h

theorem set_ct : RelCT isa (fun s₁ s₂ => R2 s₁ s₂ ∧ isa.eval .b s₁ = some false) bSet RQ :=
  RelCT.keeps [.rdx, .r9, .rdi] (by rfl)
    (taintRel [.rbp, .rdi, .rax, .r9] (fun x y ⟨⟨hs, _⟩, _⟩ r hr => hs r (List.mem_append_left (bs := [Reg.rsi, Reg.rcx]) hr))
      (by taint_decide))
    fun x y x' y' ⟨⟨hs, _⟩, _⟩ k₁ k₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> rw [k₁ _ (by decide), k₂ _ (by decide)] <;> exact same_of hs (by decide)

theorem try_ct : RelCT isa (fun s₁ s₂ => R1 s₁ s₂ ∧ isa.eval .b s₁ = some true) bTry RQ :=
  RelCT.seq load_ct (RelCT.ite (fun x y h => h.2)
    (nil_ct (P := fun s₁ s₂ => R2 s₁ s₂ ∧ isa.eval .b s₁ = some true) fun x y ⟨⟨hs, _⟩, _⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact same_of hs (by decide))
    set_ct)

theorem step_ct : RelCT isa RQ (.block [.alu .add .rsi (.imm 1), .alu .sub .rcx (.imm 1)])
    fun s₁ s₂ => s₁.zf = s₂.zf :=
  RelCT.postDep (F := fun (x x' : State) => x'.zf = some (x.gpr .rcx - 1 == 0))
    (taintRel [] nil_regs (by taint_decide))
    (fun x y _ => ⟨WP.mono (step_ok x 1) fun _ h => h.1.2.2.1, WP.mono (step_ok y 1) fun _ h => h.1.2.2.1⟩)
    fun x y x' y' e f1 f2 => by rw [f1, f2, same_of e (by decide : Reg.rcx ∈ _)]

theorem body_ct : RelCT isa BRel bBody fun s₁ s₂ => s₁.zf = s₂.zf :=
  RelCT.seq cmp_ct (RelCT.seq (RelCT.ite (fun x y h => h.2) try_ct
    (nil_ct (P := fun s₁ s₂ => R1 s₁ s₂ ∧ isa.eval .b s₁ = some false) fun x y ⟨⟨⟨hs, _⟩, _⟩, _⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact same_of hs (by decide))) step_ct)

end BallCT

/-! ## The whole function -/

namespace Ball

open BallCT

section
variable {σ₁ σ₂ : State} (hq : sbK.pub σ₁ σ₂)
include hq

theorem pub_X : X σ₁ = X σ₂ := by simp only [X, B, hq.2.2.2.2.2.2]
theorem pub_tau : tauOf σ₁ = tauOf σ₂ := by simp only [tauOf, hq.2.2.1]
theorem pub_sp : spOf σ₁ = spOf σ₂ := by simp only [spOf, hq.1, hq.2.1, hq.2.2.1, hq.2.2.2.1, hq.2.2.2.2.1]
theorem pub_St (t : Nat) : St σ₁ t = St σ₂ t := by simp only [St, i0, pub_X hq, pub_tau hq]

theorem spPub : SpPub (spOf σ₁) (spOf σ₂) σ₁ σ₂ :=
  ⟨hq.1, by simp only [hq.2.1], hq.2.2.2.2.1, hq.2.2.2.1, by simp only [hq.2.2.1], hq.2.2.2.2.2.1⟩

end

/-- Two runs at iteration `t`, `n = 264 - t` iterations from the end. -/
def LI (n : Nat) (s₁ s₂ : State) : Prop :=
  ∃ σ₁ σ₂ t, sbK.pre σ₁ ∧ sbK.pre σ₂ ∧ sbK.pub σ₁ σ₂ ∧ n = 264 - t ∧ t < 264 ∧ BAt σ₁ t s₁ ∧ BAt σ₂ t s₂

theorem li_brel {n : Nat} {s₁ s₂ : State} (h : LI n s₁ s₂) : BRel s₁ s₂ := by
  obtain ⟨σ₁, σ₂, t, p₁, p₂, hq, _, ht, l₁, l₂⟩ := h
  have rs : ∀ {σ s}, sbK.pre σ → BAt σ t s → InRegions (s.rd ++ s.wr) (s.gpr .rsi) 1 := fun hp h => by
    rw [h.rsi, at_add]; exact inScrRd (spOk hp) h.env (by omega)
  have bt : ∀ {σ s}, BAt σ t s → s.mem (s.gpr .rsi) = (X σ).getD (8 + t) 0 := fun h => by
    rw [h.rsi, at_add, show 848 + t = 840 + (8 + t) by omega, ← at_add, out_getD h.out (by omega)]
  refine ⟨fun r hr => ?_, by rw [bt l₁, bt l₂, pub_X hq], rs p₁ l₁, rs p₂ l₂⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · rw [l₁.env.rbp, l₂.env.rbp, pub_sp hq]
  · rw [l₁.rdi, l₂.rdi, pub_St hq]
  · rw [l₁.rsi, l₂.rsi, pub_sp hq]
  · rw [l₁.rcx, l₂.rcx]
  · rw [l₁.r9, l₂.r9, pub_St hq]; simp only [W, i0, pub_X hq, pub_tau hq]

theorem loop_ct (n : Nat) :
    RelCT isa (LI n) (.loop bBody .ne) (Rel2 sbK.pre sbK.pub fun σ s => BAt σ 264 s) := by
  refine RelCT.loop (M := isa) LI (fun n => ?_) n
  refine RelCT.postDep (F := fun (x x' : State) => ∀ p : State × Nat, sbK.pre p.1 ∧ p.2 < 264 ∧ BAt p.1 p.2 x →
      BAt p.1 (p.2 + 1) x' ∧ x'.zf = some (BitVec.ofNat 64 (264 - p.2) - 1 == 0))
    (RelCT.mono body_ct (fun x y h => li_brel h) fun _ _ _ => trivial) (fun x y h => ?_) ?_
  · obtain ⟨σ₁, σ₂, t, p₁, p₂, _, _, ht, l₁, l₂⟩ := h
    exact ⟨WP.all' (fun p hp' => bat_step hp'.1 hp'.2.1 hp'.2.2) ⟨(σ₁, t), p₁, ht, l₁⟩,
      WP.all' (fun p hp' => bat_step hp'.1 hp'.2.1 hp'.2.2) ⟨(σ₂, t), p₂, ht, l₂⟩⟩
  · intro x y x' y' ⟨σ₁, σ₂, t, p₁, p₂, hq, hn, ht, l₁, l₂⟩ f₁ f₂
    obtain ⟨l₁', z₁⟩ := f₁ (σ₁, t) ⟨p₁, ht, l₁⟩
    obtain ⟨l₂', z₂⟩ := f₂ (σ₂, t) ⟨p₂, ht, l₂⟩
    have ez : (BitVec.ofNat 64 (264 - t) - 1 == 0) = decide (t + 1 = 264) := by
      rw [ofNat64_pred (by omega) (by omega), ofNat64_beq_zero (by omega)]
      exact decide_eq_decide.mpr (by omega)
    rw [ez] at z₁ z₂
    refine ⟨by show x'.zf.map _ = y'.zf.map _; rw [z₁, z₂], fun hf => ?_, fun ht' => ?_⟩
    · have : t + 1 = 264 := by
        have : x'.zf.map (!·) = some false := hf
        rw [z₁] at this; simpa using this
      rw [this] at l₁' l₂'
      exact ⟨σ₁, σ₂, p₁, p₂, hq, l₁', l₂'⟩
    · have : t + 1 ≠ 264 := by
        have : x'.zf.map (!·) = some true := ht'
        rw [z₁] at this; simpa using this
      exact ⟨264 - (t + 1), by omega, σ₁, σ₂, t + 1, p₁, p₂, hq, rfl, by omega, l₁', l₂'⟩

theorem hok : ∀ σ, sbK.pre σ → SpOk (spOf σ) σ := fun _ hp => spOk hp

theorem hpub : ∀ σ₁ σ₂, sbK.pre σ₁ → sbK.pre σ₂ → sbK.pub σ₁ σ₂ → SpPub (spOf σ₁) (spOf σ₂) σ₁ σ₂ :=
  fun _ _ _ _ hq => spPub hq

/-- The zeroing, the loop and the end. -/
theorem tail_ct : RelCT isa (Rel2 sbK.pre sbK.pub fun σ => J6 136 272 (spOf σ) σ)
    (.seq bZero (.seq bLoop (.block (retJ ++ epi)))) fun _ _ => True := by
  refine RelCT.seq (relInv (I' := ZDone) (fun σ s hp h => zero_ok hp h)
    (taintSp hpub (J := J6 136 272) (fun _ _ h => h.env) [] nil_regs (by taint_decide))) ?_
  refine RelCT.seq (RelCT.seq (relInv (I' := fun σ s => WP isa (.block [.mov32 .rcx (.imm 264)]) s (BAt σ 0))
      (fun σ s hp h => setup_ok hp h)
      (taintSp hpub (J := fun P σ s => ZDone σ s) (fun _ _ h => h.env) [] nil_regs (by taint_decide)))
    (RelCT.seq (RelCT.mono (relInv (I' := fun σ s => BAt σ 0 s) (fun σ s _ h => h) (RelCT.mono
        (taintRel [] nil_regs (by taint_decide)) (fun _ _ _ => trivial) fun _ _ _ => trivial))
      (fun _ _ h => h) fun _ _ ⟨σ₁, σ₂, p₁, p₂, hq, l₁, l₂⟩ => ⟨σ₁, σ₂, 0, p₁, p₂, hq, rfl, by omega, l₁, l₂⟩)
      (loop_ct 264))) ?_
  exact taintSp hpub (J := fun P σ s => BAt σ 264 s) (fun _ _ h => h.env) [] nil_regs (by taint_decide)

end Ball

open Ball in
theorem sampleInBall_ct : ConstantTime isa sbK.pre sbK.pub Impl.MlDsa.X86_64.Sample.sampleInBall := by
  refine relStart (Q := fun _ _ => True) (RelCT.seq (relInv (I' := fun σ => J0 (spOf σ) σ)
    (fun σ s hp h => by subst h; exact pro_ok hp)
    (taintRel [.rdi, .rsi, .rcx, .r8, .rsp] (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ r hr => by
      subst h₁ h₂
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      exacts [hq.1, hq.2.1, hq.2.2.2.1, hq.2.2.2.2.1, hq.2.2.2.2.2.1]) (by taint_decide))) ?_)
  exact RelCT.seq (sponge_ct hok hpub (.inl rfl) (by decide) (by taint_decide) (by taint_decide) (by taint_decide))
    tail_ct

end VG.Proof.MlDsa.X86_64.Sample

namespace VG.Proof.MlDsa.X86_64.Sample

open VG VG.X86_64
open VG.Proof.MlDsa.Sample
open VG.Spec.MlDsa (H)
open VG.Spec.Sha3 (bytesAt)

/-- A state satisfying the precondition. -/
def sbSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 32 | .rdx => 39 | .rcx => 0x2000 | .r8 => 0x3000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 32⟩]
  wr := [⟨0x2000, 1024⟩, ⟨0x3000, 2048⟩]

theorem sampleInBall_verified :
    Verified X86_64.target Impl.MlDsa.X86_64.Sample.sampleInBall (Spec.MlDsa.sampleInBallContract X86_64.abi 16) :=
  Verified.of_correct sampleInBall_correct sampleInBall_ct
    { pre := by sig_implies_pre [Spec.MlDsa.sampleInBallContract, Spec.MlDsa.sampleInBallSig, sbK, X86_64.abi,
        X86_64.argRegs]
      post := by
        intro s s' _ h
        sig_post [Spec.MlDsa.sampleInBallContract, Spec.MlDsa.sampleInBallSig, sbK, X86_64.abi, X86_64.argRegs]
        dsimp only [sbK] at h
        obtain ⟨hr, hp⟩ := h
        by_cases hf : (ballFold (tauOf s) (H (bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat) 272)).2 = 256
        · rw [ifT hf] at hr
          obtain ⟨hred, hpoly⟩ := hp hf
          exact ⟨fun _ => hred, .inl ⟨hr, { Spec.MlDsa.minBounds with ball := 272 }, by
            show Option.map _ (Spec.MlDsa.sampleInBall _ 272 _) = _
            rw [sampleInBall_some _ (by decide) hf, hpoly]; rfl⟩⟩
        · rw [ifF hf] at hr
          exact ⟨fun h1 => absurd (hr.symm.trans h1) (by decide),
            .inr ⟨hr, by
              show Option.map _ (Spec.MlDsa.sampleInBall _ 221 _) = none
              rw [sampleInBall_none _ (B := 272) (by decide) (by decide) hf]; rfl⟩⟩
      pub := by
        intro s₁ s₂ _ _ h
        sig_pub [Spec.MlDsa.sampleInBallContract, Spec.MlDsa.sampleInBallSig, sbK, X86_64.abi,
          X86_64.argRegs] at h
        obtain ⟨hsp, hb, hdi, hsi, hdx, hcx, h8⟩ := h
        exact ⟨hdi, hsi, hdx, hcx, h8, hsp, leakBytes_inj hb⟩
      sat := by sig_implies_sat [Spec.MlDsa.sampleInBallContract, Spec.MlDsa.sampleInBallSig, sbK, X86_64.abi,
        X86_64.argRegs] [sbSat] using sbSat }

end VG.Proof.MlDsa.X86_64.Sample
