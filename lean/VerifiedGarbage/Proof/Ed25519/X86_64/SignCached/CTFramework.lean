import VerifiedGarbage.Proof.Ed25519.X86_64.SignCached.Body
import VerifiedGarbage.Proof.Framework.X86_64.Taint

/-! Relating complete signing runs with equal pointers and lengths; all input bytes remain secret. -/
namespace VG.Proof.Ed25519.X86_64.SignCached
open VG VG.X86_64
open VG.Proof.Ed25519.X86_64.PublicKey (Within)

abbrev Two.Env := Lay × (Reg → BitVec 64) × (Reg → BitVec 64) × BitVec 32 × BitVec 32 × Mem × Mem

def Two (Φ : Lay → Mem → State → Prop) (a b : State) : Prop :=
  ∃ e : Two.Env, e.1.Ok ∧
    Ctx e.1 e.2.1 e.2.2.2.1 e.2.2.2.2.2.1 a ∧ Ctx e.1 e.2.2.1 e.2.2.2.2.1 e.2.2.2.2.2.2 b ∧
    Φ e.1 e.2.2.2.2.2.1 a ∧ Φ e.1 e.2.2.2.2.2.2 b

theorem two_wp {c : Prog isa} {Φ Ψ : Lay → Mem → State → Prop}
    (hct : RelCT isa (Two Φ) c fun _ _ => True)
    (hw : ∀ (L : Lay) g mx m₀ (t : State), L.Ok → Ctx L g mx m₀ t → Φ L m₀ t →
      WP isa c t fun t' => Ctx L g mx m₀ t' ∧ Ψ L m₀ t') :
    RelCT isa (Two Φ) c (Two Ψ) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨ht, -⟩ := hct _ _ _ _ _ _ hp e₁ e₂
  obtain ⟨⟨L, g₁, g₂, mx₁, mx₂, m₁, m₂⟩, hL, c₁, c₂, f₁, f₂⟩ := hp
  obtain ⟨_, u₁, x₁, y₁⟩ := hw L g₁ mx₁ m₁ s₁ hL c₁ f₁
  obtain ⟨_, u₂, x₂, y₂⟩ := hw L g₂ mx₂ m₂ s₂ hL c₂ f₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ x₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ x₂
  exact ⟨ht, ⟨L, g₁, g₂, mx₁, mx₂, m₁, m₂⟩, hL, y₁.1, y₂.1, y₁.2, y₂.2⟩

theorem two_block {is : List Instr} {Φ : Lay → Mem → State → Prop}
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (h : (taint.check (Taint.ofRegs [.rsp]) (.block is) hc).isSome = true) :
    RelCT isa (Two Φ) (.block is) fun _ _ => True :=
  RelCT.taint (A := taint) (Taint.ofRegs [.rsp]) (fun _ _ ⟨_, _, c₁, c₂, _, _⟩ =>
    Taint.agree_ofRegs (by
      intro r hr
      simp only [List.mem_singleton] at hr; subst hr
      exact c₁.rsp.trans c₂.rsp.symm)) h

theorem two_blk {is : List Instr} {Φ Ψ : Lay → Mem → State → Prop}
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (h : (taint.check (Taint.ofRegs [.rsp]) (.block is) hc).isSome = true)
    (hw : ∀ (L : Lay) g mx m₀ (t : State), L.Ok → Ctx L g mx m₀ t → Φ L m₀ t →
      WP isa (.block is) t fun t' => Ctx L g mx m₀ t' ∧ Ψ L m₀ t') :
    RelCT isa (Two Φ) (.block is) (Two Ψ) := two_wp (two_block h) hw

structure Access (L : Lay) (rd wr : List Region) : Prop where
  sub : ∀ r ∈ rd ++ wr, ∃ R ∈ L.inputs ++ [L.FR, L.OUT, L.SCR], Within r R
  wsub : ∀ r ∈ wr, Within r L.DATA ∨ Within r L.OUT ∨ Within r L.SCR

theorem covers {L : Lay} {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem} {t : State}
    (hc : Ctx L g mx m₀ t) {rd wr : List Region} (ha : Access L rd wr) :
    Covers (rd ++ wr) (t.rd ++ t.wr) ∧ Covers wr t.wr := by
  constructor <;> apply Covers.of_sub <;> intro r hr
  · obtain ⟨R, hR, hs⟩ := ha.sub r hr
    exact ⟨R, by rw [hc.rd, hc.wr]; exact hR, hs⟩
  · rw [hc.wr]
    rcases ha.wsub r hr with h | h | h
    · obtain ⟨off, hb, hn⟩ := h
      exact ⟨L.FR, by simp, off, hb, Nat.le_trans hn (by show 192 ≤ 248; decide)⟩
    · exact ⟨L.OUT, by simp, h⟩
    · exact ⟨L.SCR, by simp, h⟩

theorem two_call {n : String} {c : Prog isa} {k : Contract isa} {Φ : Lay → Mem → State → Prop}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hct : ConstantTime isa k.pre k.pub c) (rd wr : Lay → List Region)
    (hpre : ∀ (L : Lay) g mx m₀ (t : State), L.Ok → Ctx L g mx m₀ t → Φ L m₀ t →
      k.pre (t.callEntry.withRegions (rd L) (wr L)))
    (hpub : ∀ L t₁ t₂ g₁ g₂ mx₁ mx₂ m₁ m₂, L.Ok →
      Ctx L g₁ mx₁ m₁ t₁ → Ctx L g₂ mx₂ m₂ t₂ → Φ L m₁ t₁ → Φ L m₂ t₂ →
      k.pub (t₁.callEntry.withRegions (rd L) (wr L)) (t₂.callEntry.withRegions (rd L) (wr L)))
    (ha : ∀ L, L.Ok → Access L (rd L) (wr L)) :
    RelCT isa (Two Φ) (.call n c) fun _ _ => True :=
  RelCT.callEx hv hct fun _ _ ⟨⟨L, _⟩, hL, c₁, c₂, f₁, f₂⟩ =>
    ⟨rd L, wr L, rd L, wr L, hpre _ _ _ _ _ hL c₁ f₁, hpre _ _ _ _ _ hL c₂ f₂,
      hpub _ _ _ _ _ _ _ _ _ hL c₁ c₂ f₁ f₂,
      (covers c₁ (ha L hL)).1, (covers c₁ (ha L hL)).2, (covers c₂ (ha L hL)).1, (covers c₂ (ha L hL)).2,
      c₁.rsp.trans c₂.rsp.symm⟩

theorem two_callP {n : String} {c : Prog isa} {k : Contract isa} {Φ : Lay → Mem → State → Prop}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hct : ConstantTime isa k.pre k.pub c) (hsp : NoSp c) (hd : c.depth ≤ 1) (rd wr : Lay → List Region)
    (hpre : ∀ (L : Lay) g mx m₀ (t : State), L.Ok → Ctx L g mx m₀ t → Φ L m₀ t →
      k.pre (t.callEntry.withRegions (rd L) (wr L)))
    (hpub : ∀ L t₁ t₂ g₁ g₂ mx₁ mx₂ m₁ m₂, L.Ok →
      Ctx L g₁ mx₁ m₁ t₁ → Ctx L g₂ mx₂ m₂ t₂ → Φ L m₁ t₁ → Φ L m₂ t₂ →
      k.pub (t₁.callEntry.withRegions (rd L) (wr L)) (t₂.callEntry.withRegions (rd L) (wr L)))
    (ha : ∀ L, L.Ok → Access L (rd L) (wr L)) :
    RelCT isa (Two Φ) (.call n c) (Two fun _ _ _ => True) :=
  two_wp (two_call hv hct rd wr hpre hpub ha) fun L _ _ _ _ hL hc hf =>
    call_ok hL hv hsp hd hc (hpre _ _ _ _ _ hL hc hf) (ha L hL).sub (ha L hL).wsub
      fun _ hc' _ _ _ => ⟨hc', trivial⟩

end VG.Proof.Ed25519.X86_64.SignCached
