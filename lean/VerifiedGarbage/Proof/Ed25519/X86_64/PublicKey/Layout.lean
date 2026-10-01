import VerifiedGarbage.Impl.Ed25519.X86_64.PublicKey
import VerifiedGarbage.Proof.Framework.X86_64.Frame
import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Spec.Ed25519.Contract

/-!
# Ed25519 public-key derivation on x86-64: where everything is

Untrusted: everything here is checked by Lean. The function's buffers
(`out`, `seed`, `scratch`) and the 72 bytes of stack below its return
address, from `B` up (`Lay`): the frame (56 bytes, from `B + 16`: the
pruned scalar, then the pointers to `scratch`, `seed` and `out`) and the 16
bytes below it that the calls use. `Ctx` is what holds between the
frame's push and pop: the permissions, `rsp`, the callee-saved registers,
the pointers in the frame, and that memory changed only in `out`,
`scratch` and the stack. `call_ok` runs a call of verified code in such a
state.
-/

namespace VG.Proof.Ed25519.X86_64.PublicKey

open VG VG.X86_64

/-- The buffers and the lowest byte of the stack used (`rsp - 72` on entry). -/
structure Lay where
  out : Addr
  seed : Addr
  scr : Addr
  B : Addr

namespace Lay

variable (L : Lay)

abbrev OUT : Region := ⟨L.out, 32⟩
abbrev SEED : Region := ⟨L.seed, 32⟩
abbrev SCR : Region := ⟨L.scr, 8192⟩
/-- The stack used. -/
abbrev STK : Region := ⟨L.B, 72⟩
/-- The frame. -/
abbrev FR : Region := ⟨L.B + BitVec.ofNat 64 16, 56⟩
/-- The return address. -/
abbrev RET : Region := ⟨L.B + BitVec.ofNat 64 72, 8⟩

/-- What the contract says of where the buffers and the stack are. -/
structure Ok : Prop where
  os : L.OUT.Disjoint L.SEED
  oc : L.OUT.Disjoint L.SCR
  sc : L.SEED.Disjoint L.SCR
  ko : L.STK.Disjoint L.OUT
  ks : L.STK.Disjoint L.SEED
  kc : L.STK.Disjoint L.SCR
  ro : L.RET.Disjoint L.OUT
  rs : L.RET.Disjoint L.SEED
  rc : L.RET.Disjoint L.SCR
  no : L.out.toNat + 32 ≤ 2 ^ 64
  ns : L.seed.toNat + 32 ≤ 2 ^ 64
  nc : L.scr.toNat + 8192 ≤ 2 ^ 64

end Lay

/-! ## Regions within the buffers and the stack -/

/-- `r` lies at an offset within `R`. -/
def Within (r R : Region) : Prop := ∃ off, r.base = R.base + BitVec.ofNat 64 off ∧ off + r.len ≤ R.len

theorem Within.sub {r R : Region} (h : Within r R) : Region.Sub r R := by
  obtain ⟨off, hb, hl⟩ := h
  obtain ⟨b, n⟩ := r
  simp only at hb hl
  subst hb
  exact Offset.sub_base _ hl

theorem within_off (p : Addr) {d n k : Nat} (h : d + n ≤ k) :
    Within ⟨p + BitVec.ofNat 64 d, n⟩ ⟨p, k⟩ := ⟨d, rfl, h⟩

theorem within_base (p : Addr) {n k : Nat} (h : n ≤ k) : Within ⟨p, n⟩ ⟨p, k⟩ :=
  ⟨0, (BitVec.add_zero p).symm, by simpa using h⟩

theorem within_stk (B : Addr) {d n : Nat} (h₁ : 16 ≤ d) (h₂ : d + n ≤ 72) :
    Within ⟨B + BitVec.ofNat 64 d, n⟩ ⟨B + BitVec.ofNat 64 16, 56⟩ :=
  ⟨d - 16, by rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.add_sub_cancel' h₁], by simp only; omega⟩

namespace Lay.Ok

variable {L : Lay}

theorem stk_scr (h : L.Ok) {d n e k : Nat} (h₁ : d + n ≤ 72) (h₂ : e + k ≤ 8192) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ ⟨L.scr + BitVec.ofNat 64 e, k⟩ :=
  (h.kc.sub_left (Offset.sub_base _ h₁)).sub_right (Offset.sub_base _ h₂)

theorem stk_out (h : L.Ok) {d n e k : Nat} (h₁ : d + n ≤ 72) (h₂ : e + k ≤ 32) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ ⟨L.out + BitVec.ofNat 64 e, k⟩ :=
  (h.ko.sub_left (Offset.sub_base _ h₁)).sub_right (Offset.sub_base _ h₂)

theorem stk_seed (h : L.Ok) {d n e k : Nat} (h₁ : d + n ≤ 72) (h₂ : e + k ≤ 32) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ ⟨L.seed + BitVec.ofNat 64 e, k⟩ :=
  (h.ks.sub_left (Offset.sub_base _ h₁)).sub_right (Offset.sub_base _ h₂)

theorem seed_scr (h : L.Ok) {e k : Nat} (h₂ : e + k ≤ 8192) :
    Region.Disjoint ⟨L.seed, 32⟩ ⟨L.scr + BitVec.ofNat 64 e, k⟩ :=
  h.sc.sub_right (Offset.sub_base _ h₂)

theorem out_scr (h : L.Ok) {e k : Nat} (h₂ : e + k ≤ 8192) :
    Region.Disjoint ⟨L.out, 32⟩ ⟨L.scr + BitVec.ofNat 64 e, k⟩ :=
  h.oc.sub_right (Offset.sub_base _ h₂)

theorem stk_SEED (h : L.Ok) {d n : Nat} (h₁ : d + n ≤ 72) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ L.SEED := h.ks.sub_left (Offset.sub_base _ h₁)

theorem stk_OUT (h : L.Ok) {d n : Nat} (h₁ : d + n ≤ 72) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ L.OUT := h.ko.sub_left (Offset.sub_base _ h₁)

theorem stk_SCR (h : L.Ok) {d n : Nat} (h₁ : d + n ≤ 72) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ L.SCR := h.kc.sub_left (Offset.sub_base _ h₁)

end Lay.Ok

/-- `B + 16 - 8 = B + 8`. -/
theorem sub8 (B : Addr) : B + BitVec.ofNat 64 16 - 8 = B + BitVec.ofNat 64 8 := by
  bv_omega

theorem sub8' (B : Addr) : B + BitVec.ofNat 64 16 - BitVec.ofNat 64 8 = B + BitVec.ofNat 64 8 :=
  sub8 B

/-- The stack a call from `rsp = B + 16` uses, if it nests calls at most twice. -/
theorem below_call_sub (B : Addr) {m : Nat} (hm : m ≤ 16) :
    Region.Sub (below (B + BitVec.ofNat 64 16) m) ⟨B, 16⟩ := by
  have : B + BitVec.ofNat 64 16 - BitVec.ofNat 64 m = B + BitVec.ofNat 64 (16 - m) := by
    rw [Offset.sub_ofNat_eq (B + BitVec.ofNat 64 16) (a := m) (b := 16) hm, BitVec.add_sub_cancel]
  show Region.Sub ⟨B + BitVec.ofNat 64 16 - BitVec.ofNat 64 m, m⟩ _
  rw [this]
  exact Offset.sub_base _ (by omega)

/-! ## Between the frame's push and pop -/

/-- The state between the frame's push and pop: `g` and `mx` are the
registers and MXCSR on entry, `m₀` the memory. -/
structure Ctx (L : Lay) (g : Reg → BitVec 64) (mx : BitVec 32) (m₀ : Mem) (t : State) : Prop where
  rd : t.rd = [L.SEED]
  wr : t.wr = [L.FR, L.OUT, L.SCR]
  rsp : t.gpr .rsp = L.B + BitVec.ofNat 64 16
  cs : ∀ r ∈ calleeSaved, r ≠ .rsp → t.gpr r = g r
  mx : t.mxcsr.extractLsb' 6 10 = mx.extractLsb' 6 10
  pScr : t.mem.readW (L.B + BitVec.ofNat 64 48) 64 = L.scr
  pSeed : t.mem.readW (L.B + BitVec.ofNat 64 56) 64 = L.seed
  pOut : t.mem.readW (L.B + BitVec.ofNat 64 64) 64 = L.out
  frame : Frame [L.OUT, L.SCR, L.STK] m₀ t.mem

/-- A call of verified code (see `WP.call`), which nests calls at most once
more and is given regions within `seed`, the frame, `out` and `scratch` to
read and within `out` and `scratch` to write: afterwards `Ctx` holds again,
memory changed only within what it writes and the 16 bytes below `rsp`, and
the callee's postcondition holds. -/
theorem call_ok {L : Lay} (hL : L.Ok) {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem}
    {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hsp : NoSp c) (hd : c.depth ≤ 1) {t : State} (hc : Ctx L g mx m₀ t)
    {rd wr : List Region} (hpre : k.pre (t.callEntry.withRegions rd wr))
    (hsub : ∀ r ∈ rd ++ wr, ∃ R ∈ [L.SEED, L.FR, L.OUT, L.SCR], Within r R)
    (hwsub : ∀ r ∈ wr, Within r L.OUT ∨ Within r L.SCR) {Q : State → Prop}
    (hQ : ∀ s', Ctx L g mx m₀ s' → Frame (wr ++ [⟨L.B, 16⟩]) t.mem s'.mem →
      (∀ r, (∀ i ∈ instrs c, Taint.clobbers i r = false) → s'.gpr r = t.gpr r) →
      (∃ s₂ : State, s₂.mem = s'.mem ∧ (∀ r, r ≠ .rsp → s₂.gpr r = s'.gpr r) ∧
        k.post (t.callEntry.withRegions rd wr) s₂) → Q s') :
    WP isa (.call n c) t Q := by
  have hcov : Covers (rd ++ wr) (t.rd ++ t.wr) := by
    refine Covers.of_sub fun r hr => ?_
    obtain ⟨R, hR, hw⟩ := hsub r hr
    refine ⟨R, ?_, hw⟩
    rw [hc.rd, hc.wr]
    simpa using hR
  have hcovw : Covers wr t.wr := by
    refine Covers.of_sub fun r hr => ?_
    rw [hc.wr]
    rcases hwsub r hr with h | h
    · exact ⟨_, by simp, h⟩
    · exact ⟨_, by simp, h⟩
  refine WP.call_mx hv hsp (by omega) hpre hcov hcovw fun s' hrd hwr hcs hf hg hpost hmx => ?_
  have hf' : Frame (wr ++ [⟨L.B, 16⟩]) t.mem s'.mem := by
    refine Frame.sub hf fun r hr => ?_
    rcases List.mem_append.mp hr with hr | hr
    · exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
    · simp only [List.mem_singleton] at hr; subst hr
      refine ⟨_, List.mem_append_right _ (List.mem_singleton_self _), ?_⟩
      rw [hc.rsp]
      exact below_call_sub _ (by omega)
  -- The regions the call may change are disjoint from the pointers in the frame.
  have hdisj : ∀ d, 48 ≤ d → d + 8 ≤ 72 → ∀ r ∈ wr ++ [⟨L.B, 16⟩],
      Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, 8⟩ r := by
    intro d h₁ h₂ r hr
    rcases List.mem_append.mp hr with hr | hr
    · rcases hwsub r hr with h | h
      · exact (hL.ko.sub_left (Offset.sub_base _ (by omega))).sub_right h.sub
      · exact (hL.kc.sub_left (Offset.sub_base _ (by omega))).sub_right h.sub
    · simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint_base _ (by omega) (by omega)
  have keep : ∀ d, 48 ≤ d → d + 8 ≤ 72 →
      s'.mem.readW (L.B + BitVec.ofNat 64 d) 64 = t.mem.readW (L.B + BitVec.ofNat 64 d) 64 :=
    fun d h₁ h₂ => hf'.readW (Region.contains_self _ _) (hdisj d h₁ h₂) (by decide)
  refine hQ s' ⟨hrd.trans hc.rd, hwr.trans hc.wr, ?_, fun r hr hr' => (hcs r hr).trans (hc.cs r hr hr'),
    hmx.trans hc.mx, (keep 48 (by omega) (by omega)).trans hc.pScr,
    (keep 56 (by omega) (by omega)).trans hc.pSeed, (keep 64 (by omega) (by omega)).trans hc.pOut,
    hc.frame.trans (Frame.sub hf' fun r hr => ?_)⟩ hf' hg hpost
  · rw [hcs .rsp (by simp [calleeSaved]), hc.rsp]
  · rcases List.mem_append.mp hr with hr | hr
    · rcases hwsub r hr with h | h
      · exact ⟨_, by simp, h.sub⟩
      · exact ⟨_, by simp, h.sub⟩
    · simp only [List.mem_singleton] at hr; subst hr
      refine ⟨L.STK, by simp, ?_⟩
      have := Offset.sub_base L.B (d := 0) (n := 16) (k := 72) (by omega)
      simpa using this

/-! ## The contract -/

/-- The x86-64 contract of `vg_ed25519_public_key`: `Spec.Ed25519.publicKeyContract`
for 72 bytes of stack, spelled out (`out = rdi`, `seed = rsi`, `scratch = rdx`). -/
def pkLocal : Contract isa where
  pre s := 72 ≤ (s.gpr .rsp).toNat ∧ s.rd = [⟨s.gpr .rsi, 32⟩] ∧
    s.wr = [⟨s.gpr .rdi, 32⟩, ⟨s.gpr .rdx, 8192⟩] ∧
    Region.Disjoint ⟨s.gpr .rdi, 32⟩ ⟨s.gpr .rsi, 32⟩ ∧
    Region.Disjoint ⟨s.gpr .rdi, 32⟩ ⟨s.gpr .rdx, 8192⟩ ∧
    Region.Disjoint ⟨s.gpr .rsi, 32⟩ ⟨s.gpr .rdx, 8192⟩ ∧
    Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .rdi, 32⟩ ∧
    Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .rsi, 32⟩ ∧
    Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .rdx, 8192⟩ ∧
    Region.Disjoint ⟨s.gpr .rsp - BitVec.ofNat 64 72, 72⟩ ⟨s.gpr .rdi, 32⟩ ∧
    Region.Disjoint ⟨s.gpr .rsp - BitVec.ofNat 64 72, 72⟩ ⟨s.gpr .rsi, 32⟩ ∧
    Region.Disjoint ⟨s.gpr .rsp - BitVec.ofNat 64 72, 72⟩ ⟨s.gpr .rdx, 8192⟩ ∧
    (s.gpr .rdi).toNat + 32 ≤ 2 ^ 64 ∧ (s.gpr .rsi).toNat + 32 ≤ 2 ^ 64 ∧
    (s.gpr .rdx).toNat + 8192 ≤ 2 ^ 64
  post s s' := Spec.Ed25519.bytesAt s'.mem (s.gpr .rdi) 32 =
    Spec.Ed25519.publicKey (Spec.Ed25519.bytesAt s.mem (s.gpr .rsi) 32)
  pub s₁ s₂ := s₁.gpr .rsp = s₂.gpr .rsp ∧ s₁.gpr .rdi = s₂.gpr .rdi ∧
    s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx

/-- The layout of a call from `s`. -/
def lay (s : State) : Lay := ⟨s.gpr .rdi, s.gpr .rsi, s.gpr .rdx, s.gpr .rsp - BitVec.ofNat 64 72⟩

theorem lay_ret (s : State) : (lay s).B + BitVec.ofNat 64 72 = s.gpr .rsp := BitVec.sub_add_cancel _ _

theorem lay_ok {s : State} (h : pkLocal.pre s) : (lay s).Ok := by
  obtain ⟨-, -, -, os, oc, sc, ro, rs, rc, ko, ks, kc, no, ns, nc⟩ := h
  have e : (lay s).RET = ⟨s.gpr .rsp, 8⟩ := by simp only [Lay.RET, lay_ret]
  exact ⟨os, oc, sc, ko, ks, kc, e ▸ ro, e ▸ rs, e ▸ rc, no, ns, nc⟩

end VG.Proof.Ed25519.X86_64.PublicKey
