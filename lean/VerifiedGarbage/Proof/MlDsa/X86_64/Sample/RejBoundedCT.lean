import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.RejBounded
import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.RejNttCT

/-!
# ML-DSA on x86-64: `vg_mldsa_rej_bounded_poly`, constant time but for which half-bytes it accepts

Two runs whose leaks agree (which half-bytes of the first 1088 bytes of output
are accepted, `rejBoundedLeak`) and whose pointers and `η` agree leak the
same: the prologue and the blocks around the loop by the taint analysis, the
sponge by `sponge_ct`, and the loop by relating the two runs iteration by
iteration. At iteration `t`, both runs have sampled as many coefficients (the
number depends only on which half-bytes were accepted, `rbFold_length_congr`),
and the byte to read has its half-bytes accepted alike (`leak_hbOks`): so each
branch goes the same way, and each store goes to the same address. The
coefficients themselves are computed and stored by code that the taint
analysis proves leaks nothing of them (`tryTrace`).
-/

namespace VG.Proof.MlDsa.X86_64.Sample

open VG VG.X86_64
open VG.Proof.MlKem.X86_64
open VG.Impl.MlDsa.X86_64.Sample
open VG.Proof.MlDsa.Sample
open VG.Spec.MlDsa (Zq q H halfByteOk)
open VG.Spec.Sha3 (bytesAt)

namespace RejBoundedCT

theorem halfByteOk_eq {η : Nat} (hη : η = 2 ∨ η = 4) (b : Nat) :
    halfByteOk η b = if b < rbB η then 1 else 0 := by
  unfold halfByteOk
  rw [coeffFromHalfByte_eq hη]
  by_cases h : b < rbB η <;> simp [h]

/-- Half-bytes accepted alike. -/
theorem lt_rbB_congr {η : Nat} (hη : η = 2 ∨ η = 4) {b₁ b₂ : Nat} (h : halfByteOk η b₁ = halfByteOk η b₂) :
    decide (b₁ < rbB η) = decide (b₂ < rbB η) := by
  rw [halfByteOk_eq hη, halfByteOk_eq hη] at h
  by_cases h₁ : b₁ < rbB η <;> by_cases h₂ : b₂ < rbB η <;> simp [h₁, h₂] at h ⊢

/-! ## A try -/

/-- The trace of a try depends only on `rbp`, `rdi` and whether the
half-byte is accepted. -/
theorem tryTrace {η : Nat} (hη : η = 2 ∨ η = 4) {h1 : VG.Taint.Hint X86_64.Taint.T}
    (c1 : (taint.check (X86_64.Taint.ofRegs []) (.block [.alu32 .cmp .rdx (.imm (rbBound η))]) h1).isSome = true)
    {h2 : VG.Taint.Hint X86_64.Taint.T}
    (c2 : (taint.check (X86_64.Taint.ofRegs [.rbp, .rdi])
      (.block (rbVal η ++ ([.store32 aJ .r8, .alu .add .rdi (.imm 1)] : List Instr))) h2).isSome = true)
    {h3 : VG.Taint.Hint X86_64.Taint.T} (c3 : (taint.check (X86_64.Taint.ofRegs []) (.block []) h3).isSome = true) :
    RelCT isa (fun s₁ s₂ => s₁.gpr .rbp = s₂.gpr .rbp ∧ s₁.gpr .rdi = s₂.gpr .rdi ∧
      decide (((s₁.gpr .rdx).setWidth 32).toNat < rbB η) = decide (((s₂.gpr .rdx).setWidth 32).toNat < rbB η))
      (rbTry η) fun _ _ => True := by
  refine RelCT.seq (R := fun (s₁ s₂ : State) => s₁.cf = s₂.cf ∧ s₁.gpr .rbp = s₂.gpr .rbp ∧ s₁.gpr .rdi = s₂.gpr .rdi)
    (RelCT.postDep (F := fun (x x' : State) => x'.cf = some (decide (((x.gpr .rdx).setWidth 32).toNat < rbB η)) ∧
        x'.gpr = x.gpr)
      (taintRel [] nil_regs c1)
      (fun x y _ => ⟨WP.mono (rbCmp_ok hη x) fun _ h => ⟨h.1, h.2.2.1⟩,
        WP.mono (rbCmp_ok hη y) fun _ h => ⟨h.1, h.2.2.1⟩⟩)
      fun x y x' y' ⟨e1, e2, e3⟩ ⟨f1, g1⟩ ⟨f2, g2⟩ => ⟨by rw [f1, f2, e3], by rw [g1, g2, e1], by rw [g1, g2, e2]⟩) ?_
  exact RelCT.ite (fun x y h => h.1)
    (taintRel [.rbp, .rdi] (fun x y h r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      exacts [h.1.2.1, h.1.2.2]) c2)
    (taintRel [] nil_regs c3)

/-- What a try does, from `s`, for any of its hypotheses. -/
def TryPost (η : Nat) (s s' : State) : Prop :=
  ∀ aP L b, TryPre s aP L → b < 16 → (s.gpr .rdx).setWidth 32 = BitVec.ofNat 32 b →
    s'.gpr .rdi = BitVec.ofNat 64 (hbTry η L b).length ∧ Stored s'.mem aP (hbTry η L b) ∧
      Frame [pR aP] s.mem s'.mem ∧ Keep [.rdx, .r8, .rdi] s s'

theorem rbTry_all {η : Nat} (hη : η = 2 ∨ η = 4) (s : State)
    (hne : ∃ aP L b, TryPre s aP L ∧ b < 16 ∧ (s.gpr .rdx).setWidth 32 = BitVec.ofNat 32 b) :
    WP isa (rbTry η) s (TryPost η s) := by
  have := WP.all' (Pre := fun p : Addr × List Zq × Nat =>
      TryPre s p.1 p.2.1 ∧ p.2.2 < 16 ∧ (s.gpr .rdx).setWidth 32 = BitVec.ofNat 32 p.2.2)
    (Q := fun p s' => s'.gpr .rdi = BitVec.ofNat 64 (hbTry η p.2.1 p.2.2).length ∧
      Stored s'.mem p.1 (hbTry η p.2.1 p.2.2) ∧ Frame [pR p.1] s.mem s'.mem ∧ Keep [.rdx, .r8, .rdi] s s')
    (fun p h => rbTry_ok hη s h.1 h.2.1 h.2.2) (by obtain ⟨aP, L, b, h⟩ := hne; exact ⟨(aP, L, b), h⟩)
  exact WP.mono this fun s' h aP L b hp hb hd => h (aP, L, b) ⟨hp, hb, hd⟩

/-- Two runs before a try: as many coefficients sampled, and the half-bytes
in `rdx` accepted alike. -/
def TRel (η : Nat) (s₁ s₂ : State) : Prop :=
  ∃ aP L₁ L₂ b₁ b₂, L₁.length = L₂.length ∧ TryPre s₁ aP L₁ ∧ TryPre s₂ aP L₂ ∧ b₁ < 16 ∧ b₂ < 16 ∧
    (s₁.gpr .rdx).setWidth 32 = BitVec.ofNat 32 b₁ ∧ (s₂.gpr .rdx).setWidth 32 = BitVec.ofNat 32 b₂ ∧
    halfByteOk η b₁ = halfByteOk η b₂

/-- A try, from runs related by `P`, which implies `TRel`: the final states
are related through initial ones. -/
theorem try_ct {η : Nat} (hη : η = 2 ∨ η = 4) {h1 h2 h3 : VG.Taint.Hint X86_64.Taint.T}
    (c1 : (taint.check (X86_64.Taint.ofRegs []) (.block [.alu32 .cmp .rdx (.imm (rbBound η))]) h1).isSome = true)
    (c2 : (taint.check (X86_64.Taint.ofRegs [.rbp, .rdi])
      (.block (rbVal η ++ ([.store32 aJ .r8, .alu .add .rdi (.imm 1)] : List Instr))) h2).isSome = true)
    (c3 : (taint.check (X86_64.Taint.ofRegs []) (.block []) h3).isSome = true)
    {P : State → State → Prop} (hP : ∀ s₁ s₂, P s₁ s₂ → TRel η s₁ s₂) :
    RelCT isa P (rbTry η) fun s₁' s₂' => ∃ s₁ s₂, P s₁ s₂ ∧ TryPost η s₁ s₁' ∧ TryPost η s₂ s₂' :=
  RelCT.mono (RelCT.wpDep (RelCT.mono (tryTrace hη c1 c2 c3) (fun s₁ s₂ h => by
      obtain ⟨aP, L₁, L₂, b₁, b₂, hl, t₁, t₂, hb₁, hb₂, d₁, d₂, hok⟩ := hP s₁ s₂ h
      have e₁ : ((s₁.gpr .rdx).setWidth 32).toNat = b₁ := by rw [d₁, BitVec.toNat_ofNat]; omega
      have e₂ : ((s₂.gpr .rdx).setWidth 32).toNat = b₂ := by rw [d₂, BitVec.toNat_ofNat]; omega
      exact ⟨by rw [t₁.rbp, t₂.rbp], by rw [t₁.rdi, t₂.rdi, hl], by rw [e₁, e₂]; exact lt_rbB_congr hη hok⟩)
      (fun _ _ h => h))
    (F := TryPost η) fun s₁ s₂ h => by
      obtain ⟨aP, L₁, L₂, b₁, b₂, _, t₁, t₂, hb₁, hb₂, d₁, d₂, _⟩ := hP s₁ s₂ h
      exact ⟨rbTry_all hη s₁ ⟨aP, L₁, b₁, t₁, hb₁, d₁⟩, rbTry_all hη s₂ ⟨aP, L₂, b₂, t₂, hb₂, d₂⟩⟩)
    (fun _ _ h => h) fun _ _ ⟨_, s₁, s₂, h, f₁, f₂⟩ => ⟨s₁, s₂, h, f₁, f₂⟩

/-! ## An iteration -/

/-- The hypotheses of `rbBody_ok`. -/
structure BPre (s : State) (aP : Addr) (L : List Zq) : Prop where
  rbp : s.gpr .rbp = aP
  rdi : s.gpr .rdi = BitVec.ofNat 64 L.length
  len : L.length ≤ 256
  wr : CoeffsWr s.wr aP
  st : Stored s.mem aP L
  r0 : InRegions (s.rd ++ s.wr) (s.gpr .rsi) 1

/-- Two runs at the start of an iteration, with as many coefficients sampled
and bytes to read whose half-bytes are accepted alike. -/
def BRel (η : Nat) (s₁ s₂ : State) : Prop :=
  ∃ aP L₁ L₂, L₁.length = L₂.length ∧ BPre s₁ aP L₁ ∧ BPre s₂ aP L₂ ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ hbOks η (s₁.mem (s₁.gpr .rsi)) = hbOks η (s₂.mem (s₂.gpr .rsi))

/-- The facts of a run after the loads. -/
structure MPre (s : State) (aP : Addr) (L : List Zq) (z : Byte) : Prop where
  rbp : s.gpr .rbp = aP
  rdi : s.gpr .rdi = BitVec.ofNat 64 L.length
  len : L.length ≤ 256
  wr : CoeffsWr s.wr aP
  st : Stored s.mem aP L
  cf : s.cf = some (decide (L.length < 256))
  rax : s.gpr .rax = BitVec.setWidth 64 z
  rdx : (s.gpr .rdx).setWidth 32 = BitVec.ofNat 32 (z.toNat % 16)

/-- After the loads. -/
def R1 (η : Nat) (s₁ s₂ : State) : Prop :=
  ∃ (aP : Addr) (L₁ L₂ : List Zq) (z₁ z₂ : Byte), L₁.length = L₂.length ∧ MPre s₁ aP L₁ z₁ ∧ MPre s₂ aP L₂ z₂ ∧
    hbOks η z₁ = hbOks η z₂ ∧ s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .rsi = s₂.gpr .rsi

theorem load_ct (η : Nat) : RelCT isa (BRel η) (.block rbLoad) (R1 η) := by
  refine RelCT.postDep (F := fun (x x' : State) =>
      (x'.gpr .rax = BitVec.setWidth 64 (x.mem (x.gpr .rsi)) ∧
        (x'.gpr .rdx).setWidth 32 = BitVec.ofNat 32 ((x.mem (x.gpr .rsi)).toNat % 16) ∧
        x'.cf = some (decide ((x.gpr .rdi).toNat < 256)) ∧ x'.mem = x.mem ∧ x'.gpr .rdi = x.gpr .rdi) ∧
      Keep [.rax, .rdx, .rdi] x x')
    (taintRel [.rsi] (fun x y ⟨_, _, _, _, _, _, esi, _⟩ r hr => by simp at hr; subst hr; exact esi)
      (by taint_decide))
    (fun x y ⟨_, _, _, _, p1, p2, _⟩ => ⟨rbLoad_ok x p1.r0, rbLoad_ok y p2.r0⟩) ?_
  intro x y x' y' ⟨aP, L₁, L₂, hl, p1, p2, esi, ecx, hok⟩ ⟨⟨ha, hd, hc, hm, hdi⟩, k⟩ ⟨⟨ha', hd', hc', hm', hdi'⟩, k'⟩
  have mp : ∀ {s s' : State} {L : List Zq}, BPre s aP L → s'.gpr .rax = BitVec.setWidth 64 (s.mem (s.gpr .rsi)) →
      (s'.gpr .rdx).setWidth 32 = BitVec.ofNat 32 ((s.mem (s.gpr .rsi)).toNat % 16) →
      s'.cf = some (decide ((s.gpr .rdi).toNat < 256)) → s'.mem = s.mem → s'.gpr .rdi = s.gpr .rdi →
      Keep [.rax, .rdx, .rdi] s s' → MPre s' aP L (s.mem (s.gpr .rsi)) :=
    fun {s s' L} p a d c m di kk => ⟨by rw [kk.gpr (by decide), p.rbp], by rw [di, p.rdi], p.len,
      by rw [kk.2.2]; exact p.wr, by rw [m]; exact p.st, by rw [c, p.rdi, ofNat64_toNat (by have := p.len; omega)],
      a, d⟩
  exact ⟨aP, L₁, L₂, _, _, hl, mp p1 ha hd hc hm hdi k, mp p2 ha' hd' hc' hm' hdi' k', hok,
    by rw [k.gpr (by decide), k'.gpr (by decide), ecx], by rw [k.gpr (by decide), k'.gpr (by decide), esi]⟩

/-- After the first try. -/
def R2 (η : Nat) (s₁ s₂ : State) : Prop :=
  ∃ (aP : Addr) (L₁ L₂ : List Zq) (z₁ z₂ : Byte), L₁.length = L₂.length ∧ L₁.length ≤ 256 ∧ L₂.length ≤ 256 ∧
    s₁.gpr .rbp = aP ∧ s₂.gpr .rbp = aP ∧ s₁.gpr .rdi = BitVec.ofNat 64 L₁.length ∧
    s₂.gpr .rdi = BitVec.ofNat 64 L₂.length ∧ CoeffsWr s₁.wr aP ∧ CoeffsWr s₂.wr aP ∧ Stored s₁.mem aP L₁ ∧
    Stored s₂.mem aP L₂ ∧ s₁.gpr .rax = BitVec.setWidth 64 z₁ ∧ s₂.gpr .rax = BitVec.setWidth 64 z₂ ∧
    halfByteOk η (z₁.toNat / 16) = halfByteOk η (z₂.toNat / 16) ∧ s₁.gpr .rcx = s₂.gpr .rcx ∧
    s₁.gpr .rsi = s₂.gpr .rsi

/-- Two runs before the second try (with `j < 256` in CF). -/
def R3 (η : Nat) (s₁ s₂ : State) : Prop :=
  ∃ aP L₁ L₂ b₁ b₂, L₁.length = L₂.length ∧ L₁.length ≤ 256 ∧
    s₁.gpr .rbp = aP ∧ s₂.gpr .rbp = aP ∧ s₁.gpr .rdi = BitVec.ofNat 64 L₁.length ∧
    s₂.gpr .rdi = BitVec.ofNat 64 L₂.length ∧ CoeffsWr s₁.wr aP ∧ CoeffsWr s₂.wr aP ∧ Stored s₁.mem aP L₁ ∧
    Stored s₂.mem aP L₂ ∧ b₁ < 16 ∧ b₂ < 16 ∧ (s₁.gpr .rdx).setWidth 32 = BitVec.ofNat 32 b₁ ∧
    (s₂.gpr .rdx).setWidth 32 = BitVec.ofNat 32 b₂ ∧ halfByteOk η b₁ = halfByteOk η b₂ ∧
    s₁.cf = some (decide (L₁.length < 256)) ∧ s₂.cf = some (decide (L₂.length < 256)) ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .rsi = s₂.gpr .rsi

theorem hbTry_length_eq {η : Nat} {L₁ L₂ : List Zq} (hl : L₁.length = L₂.length) {b₁ b₂ : Nat}
    (hok : halfByteOk η b₁ = halfByteOk η b₂) : (hbTry η L₁ b₁).length = (hbTry η L₂ b₂).length := by
  rw [hbTry_length, hbTry_length, hl, hok]

section
variable {η : Nat} (hη : η = 2 ∨ η = 4) {h1 h2 h3 : VG.Taint.Hint X86_64.Taint.T}
  (c1 : (taint.check (X86_64.Taint.ofRegs []) (.block [.alu32 .cmp .rdx (.imm (rbBound η))]) h1).isSome = true)
  (c2 : (taint.check (X86_64.Taint.ofRegs [.rbp, .rdi])
    (.block (rbVal η ++ ([.store32 aJ .r8, .alu .add .rdi (.imm 1)] : List Instr))) h2).isSome = true)
  (c3 : (taint.check (X86_64.Taint.ofRegs []) (.block []) h3).isSome = true)
include hη c1 c2 c3

theorem try1_ct : RelCT isa (fun s₁ s₂ => R1 η s₁ s₂ ∧ isa.eval .b s₁ = some true) (rbTry η) (R2 η) := by
  have hlt : ∀ {s₁ s₂}, (R1 η s₁ s₂ ∧ isa.eval .b s₁ = some true) → ∃ aP L₁ L₂ z₁ z₂, L₁.length = L₂.length ∧
      MPre s₁ aP L₁ z₁ ∧ MPre s₂ aP L₂ z₂ ∧ hbOks η z₁ = hbOks η z₂ ∧ s₁.gpr .rcx = s₂.gpr .rcx ∧
      s₁.gpr .rsi = s₂.gpr .rsi ∧ L₁.length < 256 := fun {s₁ s₂} ⟨⟨aP, L₁, L₂, z₁, z₂, hl, m₁, m₂, hok, e⟩, hb⟩ => by
    have : s₁.cf = some true := hb
    rw [m₁.cf] at this
    exact ⟨aP, L₁, L₂, z₁, z₂, hl, m₁, m₂, hok, e.1, e.2, by simpa using this⟩
  refine RelCT.mono (try_ct hη c1 c2 c3 fun s₁ s₂ h => ?_) (fun _ _ h => h) ?_
  · obtain ⟨aP, L₁, L₂, z₁, z₂, hl, m₁, m₂, hok, _, _, hl1⟩ := hlt h
    simp only [hbOks, Prod.mk.injEq] at hok
    exact ⟨aP, L₁, L₂, _, _, hl, ⟨m₁.rbp, m₁.rdi, hl1, m₁.wr, m₁.st⟩, ⟨m₂.rbp, m₂.rdi, by omega, m₂.wr, m₂.st⟩,
      Nat.mod_lt _ (by decide), Nat.mod_lt _ (by decide), m₁.rdx, m₂.rdx, hok.1⟩
  · intro s₁' s₂' ⟨s₁, s₂, h, f₁, f₂⟩
    obtain ⟨aP, L₁, L₂, z₁, z₂, hl, m₁, m₂, hok, ecx, esi, hl1⟩ := hlt h
    simp only [hbOks, Prod.mk.injEq] at hok
    obtain ⟨d₁, st₁, _, k₁⟩ := f₁ aP L₁ _ ⟨m₁.rbp, m₁.rdi, hl1, m₁.wr, m₁.st⟩ (Nat.mod_lt _ (by decide)) m₁.rdx
    obtain ⟨d₂, st₂, _, k₂⟩ := f₂ aP L₂ _ ⟨m₂.rbp, m₂.rdi, by omega, m₂.wr, m₂.st⟩ (Nat.mod_lt _ (by decide)) m₂.rdx
    exact ⟨aP, _, _, z₁, z₂, hbTry_length_eq hl hok.1, hbTry_length_le hl1 _, hbTry_length_le (by omega) _,
      by rw [k₁.gpr (by decide), m₁.rbp], by rw [k₂.gpr (by decide), m₂.rbp], d₁, d₂,
      by rw [k₁.2.2]; exact m₁.wr, by rw [k₂.2.2]; exact m₂.wr, st₁, st₂,
      by rw [k₁.gpr (by decide), m₁.rax], by rw [k₂.gpr (by decide), m₂.rax], hok.2,
      by rw [k₁.gpr (by decide), k₂.gpr (by decide), ecx], by rw [k₁.gpr (by decide), k₂.gpr (by decide), esi]⟩

omit hη c1 c2 c3 in
theorem hi_ct : RelCT isa (R2 η) (.block rbHi) (R3 η) := by
  refine RelCT.postDep (F := fun (x x' : State) => ∀ z : Byte, x.gpr .rax = BitVec.setWidth 64 z →
      ((x'.gpr .rdx).setWidth 32 = BitVec.ofNat 32 (z.toNat / 16) ∧
        x'.cf = some (decide ((x.gpr .rdi).toNat < 256)) ∧ x'.mem = x.mem ∧ x'.gpr .rdi = x.gpr .rdi) ∧
      Keep [.rax, .rdx, .rdi] x x')
    (taintRel [] nil_regs (by taint_decide)) (fun x y h => ?_) ?_
  · obtain ⟨_, _, _, z₁, z₂, _, _, _, _, _, _, _, _, _, _, _, a₁, a₂, _⟩ := h
    exact ⟨WP.all' (fun z hz => rbHi_ok x hz) ⟨z₁, a₁⟩, WP.all' (fun z hz => rbHi_ok y hz) ⟨z₂, a₂⟩⟩
  · intro x y x' y' ⟨aP, L₁, L₂, z₁, z₂, hl, l₁, l₂, b₁, b₂, d₁, d₂, w₁, w₂, st₁, st₂, a₁, a₂, hok, ecx, esi⟩ f₁ f₂
    obtain ⟨⟨hd₁, hc₁, hm₁, hdi₁⟩, k₁⟩ := f₁ z₁ a₁
    obtain ⟨⟨hd₂, hc₂, hm₂, hdi₂⟩, k₂⟩ := f₂ z₂ a₂
    exact ⟨aP, L₁, L₂, _, _, hl, l₁, by rw [k₁.gpr (by decide), b₁], by rw [k₂.gpr (by decide), b₂],
      by rw [hdi₁, d₁], by rw [hdi₂, d₂], by rw [k₁.2.2]; exact w₁, by rw [k₂.2.2]; exact w₂,
      by rw [hm₁]; exact st₁, by rw [hm₂]; exact st₂, by have := z₁.isLt; omega, by have := z₂.isLt; omega,
      hd₁, hd₂, hok, by rw [hc₁, d₁, ofNat64_toNat (by omega)], by rw [hc₂, d₂, ofNat64_toNat (by omega)],
      by rw [k₁.gpr (by decide), k₂.gpr (by decide), ecx], by rw [k₁.gpr (by decide), k₂.gpr (by decide), esi]⟩

theorem ite2_ct : RelCT isa (R3 η) (.ite .b (rbTry η) (.block []))
    fun s₁ s₂ => s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .rsi = s₂.gpr .rsi := by
  refine RelCT.ite (fun x y h => ?_) ?_ ?_
  · obtain ⟨_, _, _, _, _, hl, _, _, _, _, _, _, _, _, _, _, _, _, _, _, c₁, c₂, _⟩ := h
    show x.cf = y.cf; rw [c₁, c₂, hl]
  · refine RelCT.mono (try_ct hη c1 c2 c3 fun s₁ s₂ h => ?_) (fun _ _ h => h) ?_
    · obtain ⟨⟨aP, L₁, L₂, b₁, b₂, hl, _, p₁, p₂, d₁, d₂, w₁, w₂, st₁, st₂, hb₁, hb₂, x₁, x₂, hok, c₁, _⟩, hb⟩ := h
      have hl1 : L₁.length < 256 := by
        have : s₁.cf = some true := hb
        rw [c₁] at this; simpa using this
      exact ⟨aP, L₁, L₂, b₁, b₂, hl, ⟨p₁, d₁, hl1, w₁, st₁⟩, ⟨p₂, d₂, by omega, w₂, st₂⟩, hb₁, hb₂, x₁, x₂, hok⟩
    · intro s₁' s₂' ⟨s₁, s₂, ⟨⟨aP, L₁, L₂, b₁, b₂, hl, _, p₁, p₂, d₁, d₂, w₁, w₂, st₁, st₂, hb₁, hb₂, x₁, x₂, _, c₁, _,
        ecx, esi⟩, hb⟩, f₁, f₂⟩
      have hl1 : L₁.length < 256 := by
        have : s₁.cf = some true := hb
        rw [c₁] at this; simpa using this
      obtain ⟨_, _, _, k₁⟩ := f₁ aP L₁ b₁ ⟨p₁, d₁, hl1, w₁, st₁⟩ hb₁ x₁
      obtain ⟨_, _, _, k₂⟩ := f₂ aP L₂ b₂ ⟨p₂, d₂, by omega, w₂, st₂⟩ hb₂ x₂
      exact ⟨by rw [k₁.gpr (by decide), k₂.gpr (by decide), ecx], by rw [k₁.gpr (by decide), k₂.gpr (by decide), esi]⟩
  · refine RelCT.postDep (F := fun (x x' : State) => x' = x) (taintRel [] nil_regs (by taint_decide))
      (fun x y _ => ⟨WP.block_nil rfl, WP.block_nil rfl⟩) ?_
    intro x y x' y' ⟨⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, ecx, esi⟩, _⟩ f1 f2
    rw [f1, f2]; exact ⟨ecx, esi⟩

theorem mid_ct : RelCT isa (R1 η)
    (.ite .b (.seq (rbTry η) (.seq (.block rbHi) (.ite .b (rbTry η) (.block [])))) (.block []))
    fun s₁ s₂ => s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .rsi = s₂.gpr .rsi := by
  refine RelCT.ite (fun x y ⟨_, _, _, _, _, hl, m₁, m₂, _⟩ => by show x.cf = y.cf; rw [m₁.cf, m₂.cf, hl]) ?_ ?_
  · exact RelCT.seq (try1_ct hη c1 c2 c3) (RelCT.seq hi_ct (ite2_ct hη c1 c2 c3))
  · refine RelCT.postDep (F := fun (x x' : State) => x' = x) (taintRel [] nil_regs (by taint_decide))
      (fun x y _ => ⟨WP.block_nil rfl, WP.block_nil rfl⟩) ?_
    intro x y x' y' ⟨⟨_, _, _, _, _, _, _, _, _, ecx, esi⟩, _⟩ f1 f2
    rw [f1, f2]; exact ⟨ecx, esi⟩

omit hη c1 c2 c3 in
theorem step_ct : RelCT isa (fun s₁ s₂ => s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .rsi = s₂.gpr .rsi)
    (.block [.alu .add .rsi (.imm 1), .alu .sub .rcx (.imm 1)]) fun s₁ s₂ => s₁.zf = s₂.zf :=
  RelCT.postDep (F := fun (x x' : State) => x'.zf = some (x.gpr .rcx - 1 == 0))
    (taintRel [] nil_regs (by taint_decide))
    (fun x y _ => ⟨WP.mono (step_ok x 1) fun _ h => h.1.2.2.1, WP.mono (step_ok y 1) fun _ h => h.1.2.2.1⟩)
    fun x y x' y' e f1 f2 => by rw [f1, f2, e.1]

theorem body_ct : RelCT isa (BRel η) (rbBody η) fun s₁ s₂ => s₁.zf = s₂.zf :=
  RelCT.seq (load_ct η) (RelCT.seq (mid_ct hη c1 c2 c3) step_ct)

end

end RejBoundedCT

/-! ## The whole function -/

namespace RejBounded

open RejBoundedCT

section
variable {σ₁ σ₂ : State} (hq : rbK.pub σ₁ σ₂)
include hq

theorem pub_eta : etaOf σ₁ = etaOf σ₂ := by simp only [etaOf, hq.2.1]
theorem pub_sp : spOf σ₁ = spOf σ₂ := by simp only [spOf, hq.1, hq.2.1, hq.2.2.1, hq.2.2.2.1]
theorem pub_aP : σ₁.gpr .rdx = σ₂.gpr .rdx := hq.2.2.1

theorem spPub : SpPub (spOf σ₁) (spOf σ₂) σ₁ σ₂ :=
  ⟨hq.1, rfl, hq.2.2.2.1, hq.2.2.1, by simp only [hq.2.1], hq.2.2.2.2.1⟩

/-- The half-bytes of the output are accepted alike in both runs. -/
theorem pub_oks : (X σ₁).map (hbOks (etaOf σ₁)) = (X σ₂).map (hbOks (etaOf σ₁)) := by
  have h := hq.2.2.2.2.2
  rw [← pub_eta hq] at h
  exact leak_hbOks h (B := 544) (by decide)

theorem pub_len (t : Nat) : (Lt σ₁ t).length = (Lt σ₂ t).length := by
  simp only [Lt]
  rw [← pub_eta hq]
  exact rbFold_length_congr rfl (by rw [List.map_take, List.map_take, pub_oks hq])

theorem pub_ok {t : Nat} (ht : t < 544) :
    hbOks (etaOf σ₁) ((X σ₁).getD t 0) = hbOks (etaOf σ₁) ((X σ₂).getD t 0) := by
  have h := congrArg (fun L => L[t]?) (pub_oks hq)
  simp only [List.getElem?_map, List.getElem?_eq_getElem (show t < (X σ₁).length by rw [X_length]; exact ht),
    List.getElem?_eq_getElem (show t < (X σ₂).length by rw [X_length]; exact ht), Option.map_some,
    Option.some.injEq] at h
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (show t < (X σ₁).length by rw [X_length]; exact ht),
    List.getElem?_eq_getElem (show t < (X σ₂).length by rw [X_length]; exact ht)]
  exact h

end

/-- Two runs at iteration `t` of the loop for `η`, `n = 544 - t` iterations
from the end. -/
def LI (η n : Nat) (s₁ s₂ : State) : Prop :=
  ∃ σ₁ σ₂ t, rbK.pre σ₁ ∧ rbK.pre σ₂ ∧ rbK.pub σ₁ σ₂ ∧ etaOf σ₁ = η ∧ n = 544 - t ∧ t < 544 ∧
    LAt σ₁ t s₁ ∧ LAt σ₂ t s₂

theorem bpre {σ : State} (hp : rbK.pre σ) {t : Nat} (ht : t < 544) {s : State} (h : LAt σ t s) :
    BPre s (σ.gpr .rdx) (Lt σ t) :=
  ⟨h.env.rbp, h.rdi, Lt_length_le t, .of_mem (by rw [h.env.wr, hp.2.1]; simp), h.stored,
    by rw [h.rsi, at_add]; exact inScrRd (spOk hp) h.env (by omega)⟩

theorem li_brel {η n : Nat} {s₁ s₂ : State} (h : LI η n s₁ s₂) : BRel η s₁ s₂ := by
  obtain ⟨σ₁, σ₂, t, p₁, p₂, hq, he, _, ht, l₁, l₂⟩ := h
  subst he
  refine ⟨σ₁.gpr .rdx, Lt σ₁ t, Lt σ₂ t, pub_len hq t, bpre p₁ ht l₁, by rw [pub_aP hq]; exact bpre p₂ ht l₂,
    by rw [l₁.rsi, l₂.rsi, pub_sp hq], by rw [l₁.rcx, l₂.rcx], ?_⟩
  rw [out_byte l₁ ht, out_byte l₂ ht]
  exact pub_ok hq ht

theorem lat_step' {σ : State} (hp : rbK.pre σ) {η t : Nat} (he : etaOf σ = η) {s : State} (ht : t < 544)
    (h : LAt σ t s) :
    WP isa (rbBody η) s fun s' => LAt σ (t + 1) s' ∧ s'.zf = some (BitVec.ofNat 64 (544 - t) - 1 == 0) := by
  subst he; exact lat_step hp ht h

section
variable {η : Nat} (hη : η = 2 ∨ η = 4) {h1 h2 h3 : VG.Taint.Hint X86_64.Taint.T}
  (c1 : (taint.check (X86_64.Taint.ofRegs []) (.block [.alu32 .cmp .rdx (.imm (rbBound η))]) h1).isSome = true)
  (c2 : (taint.check (X86_64.Taint.ofRegs [.rbp, .rdi])
    (.block (rbVal η ++ ([.store32 aJ .r8, .alu .add .rdi (.imm 1)] : List Instr))) h2).isSome = true)
  (c3 : (taint.check (X86_64.Taint.ofRegs []) (.block []) h3).isSome = true)
include hη c1 c2 c3

theorem loop_ct (n : Nat) :
    RelCT isa (LI η n) (.loop (rbBody η) .ne) (Rel2 rbK.pre rbK.pub fun σ s => LAt σ 544 s) := by
  refine RelCT.loop (M := isa) (LI η) (fun n => ?_) n
  refine RelCT.postDep (F := fun (x x' : State) => ∀ p : State × Nat, rbK.pre p.1 ∧ etaOf p.1 = η ∧ p.2 < 544 ∧
      LAt p.1 p.2 x → LAt p.1 (p.2 + 1) x' ∧ x'.zf = some (BitVec.ofNat 64 (544 - p.2) - 1 == 0))
    (RelCT.mono (body_ct hη c1 c2 c3) (fun x y h => li_brel h) fun _ _ _ => trivial) (fun x y h => ?_) ?_
  · obtain ⟨σ₁, σ₂, t, p₁, p₂, hq, he, _, ht, l₁, l₂⟩ := h
    exact ⟨WP.all' (fun p hp' => lat_step' hp'.1 hp'.2.1 hp'.2.2.1 hp'.2.2.2) ⟨(σ₁, t), p₁, he, ht, l₁⟩,
      WP.all' (fun p hp' => lat_step' hp'.1 hp'.2.1 hp'.2.2.1 hp'.2.2.2)
        ⟨(σ₂, t), p₂, by rw [← pub_eta hq, he], ht, l₂⟩⟩
  · intro x y x' y' ⟨σ₁, σ₂, t, p₁, p₂, hq, he, hn, ht, l₁, l₂⟩ f₁ f₂
    obtain ⟨l₁', z₁⟩ := f₁ (σ₁, t) ⟨p₁, he, ht, l₁⟩
    obtain ⟨l₂', z₂⟩ := f₂ (σ₂, t) ⟨p₂, by rw [← pub_eta hq, he], ht, l₂⟩
    have ez : (BitVec.ofNat 64 (544 - t) - 1 == 0) = decide (t + 1 = 544) := by
      rw [ofNat64_pred (by omega) (by omega), ofNat64_beq_zero (by omega)]
      exact decide_eq_decide.mpr (by omega)
    rw [ez] at z₁ z₂
    refine ⟨by show x'.zf.map _ = y'.zf.map _; rw [z₁, z₂], fun hf => ?_, fun ht' => ?_⟩
    · have : t + 1 = 544 := by
        have : x'.zf.map (!·) = some false := hf
        rw [z₁] at this; simpa using this
      rw [this] at l₁' l₂'
      exact ⟨σ₁, σ₂, p₁, p₂, hq, l₁', l₂'⟩
    · have : t + 1 ≠ 544 := by
        have : x'.zf.map (!·) = some true := ht'
        rw [z₁] at this; simpa using this
      exact ⟨544 - (t + 1), by omega, σ₁, σ₂, t + 1, p₁, p₂, hq, he, rfl, by omega, l₁', l₂'⟩

/-- After the first block of the loop's setup. -/
def IA (σ s : State) : Prop :=
  Env (spOf σ) σ s ∧ bytesAt s.mem ((spOf σ).at' 840) 544 = X σ ∧ s.gpr .rsi = (spOf σ).at' 840 ∧
    s.gpr .rdi = 0

omit hη c1 c2 c3 in
theorem latB {σ s : State} (h : IA σ s) : WP isa (.block [.mov32 .rcx (.imm 544)]) s (LAt σ 0) := by
  refine WP.mono (WP.keep [.rcx] (Q := fun s' => s'.mem = s.mem ∧ s'.gpr .rcx = BitVec.ofNat 64 544)
    (by xrun) (by decide)) fun s2 ⟨⟨hm2, hcx⟩, k2⟩ => ?_
  exact ⟨h.1.keep hm2 (k2.mono (by decide)), by rw [hm2]; exact h.2.1, by rw [k2.gpr (by decide), h.2.2.1]; simp,
    by rw [k2.gpr (by decide), h.2.2.2]; rfl, hcx, by rw [hm2]; exact stored_nil _ _⟩

omit hη c1 c2 c3 in
theorem hok : ∀ σ, rbK.pre σ → SpOk (spOf σ) σ := fun _ hp => spOk hp

omit hη c1 c2 c3 in
theorem hpub : ∀ σ₁ σ₂, rbK.pre σ₁ → rbK.pre σ₂ → rbK.pub σ₁ σ₂ → SpPub (spOf σ₁) (spOf σ₂) σ₁ σ₂ :=
  fun _ _ _ _ hq => spPub hq

/-- The loop for `η`, in runs of a call with that `η`. -/
theorem rbLoop_ct : RelCT isa (Rel2 rbK.pre rbK.pub fun σ s => etaOf σ = η ∧ J6 136 544 (spOf σ) σ s)
    (rbLoop η) (Rel2 rbK.pre rbK.pub fun σ s => LAt σ 544 s) := by
  refine RelCT.seq (relInv (I' := fun σ s => etaOf σ = η ∧ IA σ s) (fun σ s _ h => WP.mono (lat0 h.2) fun _ h' =>
      ⟨h.1, h'⟩)
    (taintSp (f := spOf) hpub (J := fun P σ s => etaOf σ = η ∧ J6 136 544 P σ s) (fun _ _ h => h.2.env) []
      nil_regs (by taint_decide)))
    (RelCT.seq (RelCT.mono (relInv (I' := fun σ s => etaOf σ = η ∧ LAt σ 0 s)
        (fun σ s _ h => WP.mono (latB h.2) fun _ h' => ⟨h.1, h'⟩)
        (taintSp (f := spOf) hpub (J := fun P σ s => etaOf σ = η ∧ Env P σ s ∧
          bytesAt s.mem (P.at' 840) 544 = X σ ∧ s.gpr .rsi = P.at' 840 ∧ s.gpr .rdi = 0)
          (fun _ _ h => h.2.1) [] nil_regs (by taint_decide)))
      (fun _ _ h => h) fun _ _ ⟨σ₁, σ₂, p₁, p₂, hq, ⟨he, l₁⟩, ⟨_, l₂⟩⟩ =>
        ⟨σ₁, σ₂, 0, p₁, p₂, hq, he, rfl, by omega, l₁, l₂⟩)
      (loop_ct hη c1 c2 c3 544))

end

/-- The branch on `η`, and the loops. -/
theorem sel_ct : RelCT isa (Rel2 rbK.pre rbK.pub fun σ => J6 136 544 (spOf σ) σ)
    (.seq (.block [.alu32 .cmp .r12 (.imm 2)]) (.ite .e (rbLoop 2) (rbLoop 4)))
    (Rel2 rbK.pre rbK.pub fun σ s => LAt σ 544 s) := by
  refine RelCT.seq (relInv (I' := fun σ s => J6 136 544 (spOf σ) σ s ∧ s.zf = some (decide (etaOf σ = 2)))
    (fun σ s hp h => ?_) (taintSp hpub (fun _ _ h => h.env) [] nil_regs (by taint_decide))) ?_
  · refine WP.mono (WP.keep [.r12] (Q := fun s' => s'.mem = s.mem ∧ s'.gpr .r12 = s.gpr .r12 ∧
        s'.zf = some (BitVec.setWidth 32 (s.gpr .r12) - 2 == 0)) (by xrun) (by rfl))
      fun s1 ⟨⟨hm1, h12, hz1⟩, k1⟩ => ⟨⟨h.env.keep hm1 ⟨fun r hr => by
        by_cases e : r = .r12
        · subst e; exact h12
        · exact k1.gpr (by simp [e]), k1.2⟩, by rw [hm1]; exact h.out⟩, ?_⟩
    have hr12 : BitVec.setWidth 32 (s.gpr .r12) = BitVec.ofNat 32 (etaOf σ) := by
      rw [h.env.r12]; rw [sw32_64, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    rw [hz1, hr12]
    rcases eta hp with he | he <;> rw [he] <;> rfl
  refine RelCT.ite (fun x y ⟨σ₁, σ₂, _, _, hq, ⟨_, z₁⟩, ⟨_, z₂⟩⟩ => by
    show x.zf = y.zf; rw [z₁, z₂, pub_eta hq]) ?_ ?_
  · refine RelCT.mono (rbLoop_ct (η := 2) (.inl rfl) (by taint_decide) (by taint_decide) (by taint_decide))
      (fun x y ⟨⟨σ₁, σ₂, p₁, p₂, hq, ⟨j₁, z₁⟩, ⟨j₂, _⟩⟩, hb⟩ => ⟨σ₁, σ₂, p₁, p₂, hq, ⟨?_, j₁⟩, ⟨?_, j₂⟩⟩)
      fun _ _ h => h
    · have : x.zf = some true := hb
      rw [z₁] at this; simpa using this
    · have : x.zf = some true := hb
      rw [z₁, pub_eta hq] at this; simpa using this
  · refine RelCT.mono (rbLoop_ct (η := 4) (.inr rfl) (by taint_decide) (by taint_decide) (by taint_decide))
      (fun x y ⟨⟨σ₁, σ₂, p₁, p₂, hq, ⟨j₁, z₁⟩, ⟨j₂, _⟩⟩, hb⟩ => ⟨σ₁, σ₂, p₁, p₂, hq, ⟨?_, j₁⟩, ⟨?_, j₂⟩⟩)
      fun _ _ h => h
    · have : x.zf = some false := hb
      rw [z₁] at this
      rcases eta p₁ with he | he
      · rw [he] at this; simp at this
      · exact he
    · have : x.zf = some false := hb
      rw [z₁, pub_eta hq] at this
      rcases eta p₂ with he | he
      · rw [he] at this; simp at this
      · exact he

end RejBounded

open RejBounded in
theorem rejBounded_ct : ConstantTime isa rbK.pre rbK.pub Impl.MlDsa.X86_64.Sample.rejBounded := by
  refine relStart (Q := fun _ _ => True) (RelCT.seq (relInv (I' := fun σ => J0 (spOf σ) σ)
    (fun σ s hp h => by subst h; exact pro_ok hp)
    (taintRel [.rdi, .rdx, .rcx, .rsp] (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ r hr => by
      subst h₁ h₂
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      exacts [hq.1, hq.2.2.1, hq.2.2.2.1, hq.2.2.2.2.1]) (by taint_decide))) ?_)
  refine RelCT.seq (sponge_ct hok hpub (.inl rfl) (by decide) (by taint_decide) (by taint_decide) (by taint_decide)) ?_
  exact RelCT.seq sel_ct (taintSp (J := fun P σ s => LAt σ 544 s) hpub (fun _ _ h => h.env) [] nil_regs
    (by taint_decide))

end VG.Proof.MlDsa.X86_64.Sample

namespace VG.Proof.MlDsa.X86_64.Sample

open VG VG.X86_64
open VG.Proof.MlDsa.Sample
open VG.Spec.MlDsa (H)
open VG.Spec.Sha3 (bytesAt)

/-- A state satisfying the precondition. -/
def rbSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 2 | .rdx => 0x2000 | .rcx => 0x3000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 66⟩]
  wr := [⟨0x2000, 1024⟩, ⟨0x3000, 2048⟩]

theorem rejBounded_verified :
    Verified X86_64.target Impl.MlDsa.X86_64.Sample.rejBounded (Spec.MlDsa.rejBoundedContract X86_64.abi 16) :=
  Verified.of_correct rejBounded_correct rejBounded_ct
    { pre := by sig_implies_pre [Spec.MlDsa.rejBoundedContract, Spec.MlDsa.rejBoundedSig, rbK, X86_64.abi,
        X86_64.argRegs]
      post := by
        intro s s' _ h
        sig_post [Spec.MlDsa.rejBoundedContract, Spec.MlDsa.rejBoundedSig, rbK, X86_64.abi, X86_64.argRegs]
        dsimp only [rbK] at h
        obtain ⟨hr, hp⟩ := h
        by_cases hf : (rbFold (etaOf s) [] (H (bytesAt s.mem (s.gpr .rdi) 66) 544)).length = 256
        · rw [ifT hf] at hr
          obtain ⟨hred, hpoly⟩ := hp hf
          exact ⟨fun _ => hred, .inl ⟨hr, { Spec.MlDsa.minBounds with rejBounded := 544 }, by
            show Option.map _ (Spec.MlDsa.rejBoundedPoly _ 544 _) = _
            rw [rejBounded_some _ hf, hpoly]⟩⟩
        · rw [ifF hf] at hr
          exact ⟨fun h1 => absurd (hr.symm.trans h1) (by decide),
            .inr ⟨hr, by
              show Option.map _ (Spec.MlDsa.rejBoundedPoly _ 481 _) = none
              rw [rejBounded_none _ (B := 544) (by decide) hf]; rfl⟩⟩
      pub := by
        intro s₁ s₂ _ _ h
        sig_pub [Spec.MlDsa.rejBoundedContract, Spec.MlDsa.rejBoundedSig, rbK, X86_64.abi, X86_64.argRegs] at h
        obtain ⟨hsp, hb, hdi, hsi, hdx, hcx⟩ := h
        exact ⟨hdi, hsi, hdx, hcx, hsp, hb⟩
      sat := by sig_implies_sat [Spec.MlDsa.rejBoundedContract, Spec.MlDsa.rejBoundedSig, rbK, X86_64.abi,
        X86_64.argRegs] [rbSat] using rbSat }

end VG.Proof.MlDsa.X86_64.Sample
