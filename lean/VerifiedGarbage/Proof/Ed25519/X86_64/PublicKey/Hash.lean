import VerifiedGarbage.Impl.Ed25519.X86_64.PublicKey
import VerifiedGarbage.Proof.Framework.X86_64.Frame
import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Spec.Ed25519.Contract
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Sha512.X86_64.Compress
import VerifiedGarbage.Proof.Sha512.X86_64.Stream.Init
import VerifiedGarbage.Proof.Sha512.X86_64.Variant
import VerifiedGarbage.Proof.Sha512.Stream
import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Hashes.Sha512

/-! Merged from `Proof.Ed25519.X86_64.PublicKey.Layout`. -/
section
/-!
# Ed25519 public-key derivation on x86-64: where everything is

The function's buffers (`out`, `seed`, `scratch`) and the 72 bytes of stack
below its return address, from `B` up (`Lay`): the frame (56 bytes, from `B +
16`: the pruned scalar, then the pointers to `scratch`, `seed` and `out`) and
the 16 bytes below it that the calls use. `Ctx` is what holds between the
frame's push and pop: the permissions, `rsp`, the callee-saved registers, the
pointers in the frame, and that memory changed only in `out`, `scratch` and
the stack. `call_ok` runs a call of verified code in such a state.
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
end

/-!
# Ed25519 public-key derivation on x86-64: the hash of the seed

From the state after the frame's push (`push_ctx`), the calls of `init`,
`update` and `finalize` leave `SHA-512(seed)` at `scratch + 1568` (`hash_ok`),
for any implementation `v` of the compression function.
-/

namespace VG.Proof.Ed25519.X86_64.PublicKey

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.Sha512.X86_64 (Compress)

/-! ## Addresses -/

theorem ofInt_nat (n : Nat) : BitVec.ofInt 64 (n : Int) = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toInt_eq; simp

theorem ea_stk (t : State) (d : Nat) : t.ea (stk d) = t.gpr .rsp + BitVec.ofNat 64 d := by
  show t.gpr .rsp + BitVec.ofInt 64 (d : Int) = _
  rw [ofInt_nat]

theorem ea_base (t : State) (r : Reg) (d : Nat) :
    t.ea { base := r, disp := (d : Int) } = t.gpr r + BitVec.ofNat 64 d := by
  show t.gpr r + BitVec.ofInt 64 (d : Int) = _
  rw [ofInt_nat]

theorem add_add (p : Addr) (a b : Nat) :
    p + BitVec.ofNat 64 a + BitVec.ofNat 64 b = p + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]

theorem sx32 {n : Nat} (h : n < 2 ^ 31) : (BitVec.ofNat 32 n).signExtend 64 = BitVec.ofNat 64 n := by
  have hm : (BitVec.ofNat 32 n).msb = false := by
    rw [BitVec.msb_eq_decide]; simp only [BitVec.toNat_ofNat, decide_eq_false_iff_not]; omega
  rw [BitVec.signExtend_eq_setWidth_of_msb_false hm]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

theorem zx32 {n : Nat} (h : n < 2 ^ 32) : (BitVec.ofNat 32 n).setWidth 64 = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

/-- Byte `i` of a region the return address of a call misses, on entry to the callee. -/
theorem ce_byte (t : State) {R : Region} (hd : (below (t.gpr .rsp) 8).Disjoint R)
    (hR : R.len ≤ 2 ^ 64) {i : Nat} (hi : i < R.len) :
    t.callEntry.mem (R.base + BitVec.ofNat 64 i) = t.mem (R.base + BitVec.ofNat 64 i) :=
  Frame.bytes (rs := [below (t.gpr .rsp) 8])
    (Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _ (below_call _ (by omega) (by omega)))
    (by simpa using hd.symm) hR hi

namespace Ctx

variable {L : Lay} {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem} {t t' : State}

/-- Code that writes only caller-saved registers. -/
theorem regs (hc : Ctx L g mx m₀ t) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) (hm : t'.mem = t.mem)
    (hmx : t'.mxcsr = t.mxcsr) (hg : ∀ r ∈ calleeSaved, t'.gpr r = t.gpr r) : Ctx L g mx m₀ t' :=
  ⟨hrd.trans hc.rd, hwr.trans hc.wr, (hg .rsp (by decide)).trans hc.rsp,
    fun r hr hr' => (hg r hr).trans (hc.cs r hr hr'), by rw [hmx]; exact hc.mx,
    by rw [hm]; exact hc.pScr, by rw [hm]; exact hc.pSeed, by rw [hm]; exact hc.pOut,
    by rw [hm]; exact hc.frame⟩

/-- The return address of a call from the frame. -/
theorem ret (hc : Ctx L g mx m₀ t) : below (t.gpr .rsp) 8 = ⟨L.B + BitVec.ofNat 64 8, 8⟩ := by
  rw [hc.rsp]
  show (⟨L.B + BitVec.ofNat 64 16 - BitVec.ofNat 64 8, 8⟩ : Region) = _
  rw [sub8']

theorem ce_rsp (hc : Ctx L g mx m₀ t) : t.callEntry.gpr .rsp = L.B + BitVec.ofNat 64 8 := by
  rw [State.callEntry_rsp, hc.rsp, sub8]

/-- The seed, as on entry. -/
theorem seed (hL : L.Ok) (hc : Ctx L g mx m₀ t) {i : Nat} (hi : i < 32) :
    t.mem (L.seed + BitVec.ofNat 64 i) = m₀ (L.seed + BitVec.ofNat 64 i) :=
  Frame.bytes (R := L.SEED) hc.frame (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hL.os.symm
    · exact hL.sc
    · exact hL.ks.symm) (by show (32 : Nat) ≤ 2 ^ 64; decide) hi

/-- The seed on entry to a call from the frame. -/
theorem ce_seed (hL : L.Ok) (hc : Ctx L g mx m₀ t) :
    Spec.Ed25519.bytesAt t.callEntry.mem L.seed 32 = Spec.Ed25519.bytesAt m₀ L.seed 32 := by
  simp only [Spec.Ed25519.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  rw [ce_byte t (R := L.SEED) (by rw [hc.ret]; exact hL.stk_SEED (by omega)) (by show (32 : Nat) ≤ 2 ^ 64; decide) hi]
  exact hc.seed hL hi

theorem inFr (hc : Ctx L g mx m₀ t) {d : Nat} (h₁ : 16 ≤ d) (h₂ : d + 8 ≤ 72) :
    InRegions (t.rd ++ t.wr) (L.B + BitVec.ofNat 64 d) 8 :=
  ⟨L.FR, by rw [hc.rd, hc.wr]; simp, Offset.contains _ h₁ (by omega) (by omega)⟩

theorem inFrW (hc : Ctx L g mx m₀ t) {d : Nat} (h₁ : 16 ≤ d) (h₂ : d + 8 ≤ 72) :
    InRegions t.wr (L.B + BitVec.ofNat 64 d) 8 :=
  ⟨L.FR, by rw [hc.wr]; simp, Offset.contains _ h₁ (by omega) (by omega)⟩

theorem inScr (hc : Ctx L g mx m₀ t) {o : Nat} (h : o + 8 ≤ 8192) :
    InRegions (t.rd ++ t.wr) (L.scr + BitVec.ofNat 64 o) 8 :=
  ⟨L.SCR, by rw [hc.rd, hc.wr]; simp, Offset.contains_base _ h (by omega)⟩

theorem ea_fr (hc : Ctx L g mx m₀ t) (d : Nat) : t.ea (stk d) = L.B + BitVec.ofNat 64 (16 + d) := by
  rw [ea_stk, hc.rsp, add_add]

end Ctx

/-! ## The frame's push -/

/-- The registers the frame's push stores. -/
abbrev pushRs : List Reg := [.rdi, .rsi, .rdx, .rax, .rax, .rax, .rax]

theorem push_base (sp : Addr) :
    sp - BitVec.ofNat 64 (8 * 7) = sp - BitVec.ofNat 64 72 + BitVec.ofNat 64 16 := by bv_omega

theorem push_slot (sp : Addr) (j : Nat) (hj : j < 3) :
    sp - BitVec.ofNat 64 (8 * (j + 1)) = sp - BitVec.ofNat 64 72 + BitVec.ofNat 64 (64 - 8 * j) := by
  have : 8 * (j + 1) < 2 ^ 64 := by omega
  bv_omega

theorem push_ctx {s : State} (h : pkLocal.pre s) :
    Ctx (lay s) s.gpr s.mxcsr s.mem (pushed pushRs s) := by
  have hn : 8 * pushRs.length ≤ (s.gpr .rsp).toNat := by show 8 * 7 ≤ _; have := h.1; omega
  obtain ⟨hf, hw⟩ := pushRegs_mem s pushRs (by decide) hn
  have hw' : ∀ j (hj : j < 3), (pushed pushRs s).mem.readW
      ((lay s).B + BitVec.ofNat 64 (64 - 8 * j)) 64 = s.gpr (pushRs[j]'(by show j < 7; omega)) := fun j hj => by
    rw [← hw j (by show j < 7; omega)]; simp only [lay]; rw [push_slot _ j hj]; rfl
  refine ⟨by rw [pushed_rd, h.2.1]; rfl, ?_, ?_, fun r _ hr => pushed_gpr _ _ hr, by rw [pushed_mxcsr],
    hw' 2 (by omega), hw' 1 (by omega), hw' 0 (by omega), ?_⟩
  · rw [pushed_wr, h.2.2.1]; simp only [List.length_cons, List.length_nil, lay]; rw [push_base]
  · rw [pushed_rsp]; simp only [List.length_cons, List.length_nil, lay]; rw [push_base]
  · refine Frame.sub hf fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    refine ⟨(lay s).STK, by simp, ?_⟩
    simp only [List.length_cons, List.length_nil]
    rw [push_base]
    exact Offset.sub_base _ (by omega)

/-! ## `init` -/

theorem nosp_init (iv : Spec.Sha512.HashValue) : NoSp (Impl.Sha512.X86_64.Stream.init iv) := by
  intro i hi
  rw [Proof.Sha512.X86_64.Stream.init_eq] at hi
  simp only [instrs, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem gpr_ce (t : State) (rd wr : List Region) {r : Reg} (h : r ≠ .rsp) :
    (t.callEntry.withRegions rd wr).gpr r = t.gpr r := by
  rw [State.withRegions_gpr, State.callEntry_gpr _ h]

theorem rsp_ce (t : State) (rd wr : List Region) :
    (t.callEntry.withRegions rd wr).gpr .rsp = t.gpr .rsp - 8 := by
  rw [State.withRegions_gpr, State.callEntry_rsp]

/-- Callee-saved registers, through writes of others. -/
macro "cs_tac" : tactic => `(tactic| (
  intro r hr
  revert hr
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false]
  rintro (h | h | h | h | h | h | h) <;> subst h <;>
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, reduceCtorEq, ite_false]))

theorem ne_cs {r d : Reg} (hr : r ∈ calleeSaved) (hd : d ∉ calleeSaved) : r ≠ d :=
  fun e => hd (e ▸ hr)

variable {L : Lay} {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem}

/-- What the call of `init` needs of the registers. -/
def InitArgs (L : Lay) (t : State) : Prop := t.gpr .rdi = L.scr

abbrev initRd : List Region := []
abbrev initWr (L : Lay) : List Region := [⟨L.scr, 192⟩]

theorem initArgs_ok {t : State} (hc : Ctx L g mx m₀ t) :
    WP isa (.block pkInitArgs) t fun t' => Ctx L g mx m₀ t' ∧ t'.mem = t.mem ∧ InitArgs L t' := by
  have hin := hc.inFr (d := 48) (by omega) (by omega)
  refine WP.of_runBlock ⟨t.setReg .rdi L.scr, ?_, ?_⟩
  · simp only [pkInitArgs, fScratch, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
      State.load64, hc.ea_fr, hin, ite_true, Option.map_some, hc.pScr]
  exact ⟨hc.regs rfl rfl rfl rfl fun r hr => RegUpd.gpr_setReg_of_ne _ _ (ne_cs hr (by decide)), rfl,
    RegUpd.gpr_setReg_self _ _ _⟩

theorem init_pre (hL : L.Ok) {t : State} (hc : Ctx L g mx m₀ t) (ha : InitArgs L t) :
    (Proof.Sha512.initX86_64 Spec.Sha512.H0_512).pre (t.callEntry.withRegions initRd (initWr L)) := by
  have hrdi := (gpr_ce t initRd (initWr L) (r := .rdi) (by decide)).trans ha
  refine ⟨rfl, by rw [hrdi]; rfl, ?_⟩
  rw [rsp_ce, hrdi, hc.rsp, sub8]
  simpa using hL.stk_scr (d := 8) (n := 8) (e := 0) (k := 192) (by omega) (by omega)

theorem init_sub : ∀ r ∈ initRd ++ initWr L, ∃ R ∈ [L.SEED, L.FR, L.OUT, L.SCR], Within r R := by
  simp only [List.nil_append, List.mem_singleton]
  rintro r rfl
  exact ⟨L.SCR, by simp, within_base _ (by omega)⟩

theorem init_wsub : ∀ r ∈ initWr L, Within r L.OUT ∨ Within r L.SCR := by
  simp only [List.mem_singleton]
  rintro r rfl
  exact .inr (within_base _ (by omega))

theorem init_call (hL : L.Ok) {t : State} (hc : Ctx L g mx m₀ t) (ha : InitArgs L t) :
    WP isa (.call Spec.Sha512.init512Api.name (Impl.Sha512.X86_64.Stream.init Spec.Sha512.H0_512)) t
      fun t' => Ctx L g mx m₀ t' ∧ Spec.Sha512.Repr Spec.Sha512.H0_512 t'.mem L.scr [] := by
  refine call_ok hL (Proof.Sha512.X86_64.Stream.init_verified _).1 (nosp_init _) (by decide) hc
    (init_pre hL hc ha) init_sub init_wsub fun s' hc' _ _ ⟨s₂, hm, _, hpost⟩ => ⟨hc', ?_⟩
  have := hpost
  simp only [Proof.Sha512.initX86_64, (gpr_ce t initRd (initWr L) (r := .rdi) (by decide)).trans ha] at this
  rwa [← hm]

theorem init_step (hL : L.Ok) {t : State} (hc : Ctx L g mx m₀ t) :
    WP isa (callWith pkInitArgs Spec.Sha512.init512Api.name
      (Impl.Sha512.X86_64.Stream.init Spec.Sha512.H0_512)) t
      fun t' => Ctx L g mx m₀ t' ∧ Spec.Sha512.Repr Spec.Sha512.H0_512 t'.mem L.scr [] :=
  WP.seq (WP.mono (initArgs_ok hc) fun _ ⟨hc₁, _, ha⟩ => init_call hL hc₁ ha)

/-! ## `update` and `finalize`, for any compression function -/

/-- SHA-512 with the compression function `v`, as `MdHash` builds it. -/
abbrev hashOf (v : Compress) : Impl.Pbkdf2.Md.X86_64.Hash :=
  Proof.Pbkdf2.Md.X86_64.Sha512.hash Spec.Hmac.sha512I 64 Spec.Sha512.init512Api.name
    Spec.Sha512.H0_512 v

theorem callees (v : Compress) : Proof.Pbkdf2.Md.X86_64.Callees (hashOf v) :=
  Proof.Pbkdf2.Md.X86_64.Sha512.callees (Or.inr (Or.inl rfl)) v

theorem coreOK (v : Compress) : Proof.Pbkdf2.Md.X86_64.CoreOK (Proof.Pbkdf2.Md.X86_64.core (hashOf v)) :=
  Proof.Pbkdf2.Md.X86_64.Sha512.sha512_coreOK

theorem upd_mx (v : Compress) :
    (Impl.Sha512.X86_64.Stream.update v.callee).allInstrs (fun i => !loadsMxcsr i) = true :=
  (callees v).updMx (coreOK v)

theorem fin_mx (v : Compress) :
    (Impl.Sha512.X86_64.Stream.finalize v.callee).allInstrs (fun i => !loadsMxcsr i) = true :=
  (callees v).finMx (coreOK v)

theorem upd_nosp (v : Compress) : NoSp (Impl.Sha512.X86_64.Stream.update v.callee) :=
  (callees v).updSp (coreOK v)

theorem fin_nosp (v : Compress) : NoSp (Impl.Sha512.X86_64.Stream.finalize v.callee) :=
  (callees v).finSp (coreOK v)

theorem upd_depth (v : Compress) : (Impl.Sha512.X86_64.Stream.update v.callee).depth ≤ 1 :=
  (callees v).updD (coreOK v)

theorem fin_depth (v : Compress) : (Impl.Sha512.X86_64.Stream.finalize v.callee).depth ≤ 1 :=
  (callees v).finD (coreOK v)

theorem upd_verified (v : Compress) :
    Verified X86_64.target (Impl.Sha512.X86_64.Stream.update v.callee) Proof.Sha512.updateX86_64 :=
  Proof.Sha512.X86_64.Stream.Update.verified_of v.ok (upd_mx v)

theorem fin_verified (v : Compress) :
    Verified X86_64.target (Impl.Sha512.X86_64.Stream.finalize v.callee) Proof.Sha512.finalizeX86_64 :=
  Proof.Sha512.X86_64.Stream.Finalize.verified_of v.ok (fin_mx v)

theorem cs_keep {t : State} {d : Reg} (v : BitVec 64) (hd : d ∉ calleeSaved) :
    ∀ r ∈ calleeSaved, (t.setReg d v).gpr r = t.gpr r :=
  fun _ hr => RegUpd.gpr_setReg_of_ne _ _ (ne_cs hr hd)

/-- What the call of `update` needs of the registers. -/
def UpdArgs (L : Lay) (t : State) : Prop :=
  t.gpr .rdi = L.scr ∧ t.gpr .rsi = 0 ∧ t.gpr .rdx = L.seed ∧ t.gpr .rcx = BitVec.ofNat 64 32 ∧
    t.gpr .r8 = L.scr + BitVec.ofNat 64 192

theorem updArgs_ok {t : State} (hc : Ctx L g mx m₀ t) :
    WP isa (.block pkUpdateArgs) t fun t' => Ctx L g mx m₀ t' ∧ t'.mem = t.mem ∧ UpdArgs L t' := by
  have h48 := hc.inFr (d := 48) (by omega) (by omega)
  have h56 := hc.inFr (d := 56) (by omega) (by omega)
  apply WP.of_runBlock
  simp only [pkUpdateArgs, scrPtr, shaScratch, fScratch, fSeed, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, readSrc32, State.load64,
    State.setReg32, ea_stk, RegUpd.gpr_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg,
    RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags,
    Option.map_some, Option.bind_some, reduceCtorEq, ite_false, ite_true, hc.rsp, add_add,
    Nat.reduceAdd, h48, h56, Option.some.injEq, exists_eq_left', hc.pScr, hc.pSeed, UpdArgs]
  exact ⟨hc.regs rfl rfl rfl rfl (by cs_tac), trivial, trivial, rfl, trivial, rfl, by rw [sx32 (by omega)]⟩

theorem sub88 (B : Addr) : B + BitVec.ofNat 64 8 - 8 = B := by bv_omega

/-- The state at `scratch`, on entry to a call from the frame. -/
theorem Ctx.ce_repr (hL : L.Ok) {t : State} (hc : Ctx L g mx m₀ t) {iv : Spec.Sha512.HashValue}
    {m : List Byte} (hr : Spec.Sha512.Repr iv t.mem L.scr m) : Spec.Sha512.Repr iv t.callEntry.mem L.scr m :=
  Proof.Sha512.Stream.repr_congr (fun i hi => ce_byte t (R := ⟨L.scr, 192⟩)
    (by rw [hc.ret]; simpa using hL.stk_scr (d := 8) (n := 8) (e := 0) (k := 192) (by omega) (by omega))
    (by show (192 : Nat) ≤ 2 ^ 64; decide) hi) hr

abbrev updRd (L : Lay) : List Region := [L.SEED]
abbrev updWr (L : Lay) : List Region := [⟨L.scr, 192⟩, ⟨L.scr + BitVec.ofNat 64 192, 1376⟩]

theorem upd_regs {t : State} (ha : UpdArgs L t) (rd wr : List Region) :
    (t.callEntry.withRegions rd wr).gpr .rdi = L.scr ∧ (t.callEntry.withRegions rd wr).gpr .rsi = 0 ∧
      (t.callEntry.withRegions rd wr).gpr .rdx = L.seed ∧
      (t.callEntry.withRegions rd wr).gpr .rcx = BitVec.ofNat 64 32 ∧
      (t.callEntry.withRegions rd wr).gpr .r8 = L.scr + BitVec.ofNat 64 192 :=
  ⟨(gpr_ce _ _ _ (by decide)).trans ha.1, (gpr_ce _ _ _ (by decide)).trans ha.2.1,
    (gpr_ce _ _ _ (by decide)).trans ha.2.2.1, (gpr_ce _ _ _ (by decide)).trans ha.2.2.2.1,
    (gpr_ce _ _ _ (by decide)).trans ha.2.2.2.2⟩

theorem upd_pre (hL : L.Ok) {t : State} (hc : Ctx L g mx m₀ t) (ha : UpdArgs L t) :
    Proof.Sha512.updateX86_64.pre (t.callEntry.withRegions (updRd L) (updWr L)) := by
  obtain ⟨hdi, -, hdx, hcx, h8⟩ := upd_regs ha (updRd L) (updWr L)
  simp only [Proof.Sha512.updateX86_64, rsp_ce, hdi, hdx, hcx, h8, hc.rsp, sub8, sub88,
    State.withRegions_rd, State.withRegions_wr]
  exact ⟨by first | trivial | rfl, by first | trivial | rfl, Offset.base_disjoint _ (by omega) (by omega),
    by simpa using hL.seed_scr (e := 0) (k := 192) (by omega), hL.seed_scr (by omega),
    by simpa using hL.stk_scr (d := 8) (n := 8) (e := 0) (k := 192) (by omega) (by omega),
    hL.stk_scr (d := 8) (n := 8) (by omega) (by omega),
    by simpa using hL.stk_scr (d := 0) (n := 8) (e := 0) (k := 192) (by omega) (by omega),
    by simpa using hL.stk_SEED (d := 0) (n := 8) (by omega),
    by simpa using hL.stk_scr (d := 0) (n := 8) (e := 192) (k := 1376) (by omega) (by omega)⟩

theorem upd_sub : ∀ r ∈ updRd L ++ updWr L, ∃ R ∈ [L.SEED, L.FR, L.OUT, L.SCR], Within r R := by
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact ⟨L.SEED, by simp, within_base _ (by omega)⟩
  · exact ⟨L.SCR, by simp, within_base _ (by omega)⟩
  · exact ⟨L.SCR, by simp, within_off _ (by omega)⟩

theorem upd_wsub : ∀ r ∈ updWr L, Within r L.OUT ∨ Within r L.SCR := by
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact .inr (within_base _ (by omega))
  · exact .inr (within_off _ (by omega))

theorem upd_call (v : Compress) (hL : L.Ok) {t : State} (hc : Ctx L g mx m₀ t) (ha : UpdArgs L t)
    (hr : Spec.Sha512.Repr Spec.Sha512.H0_512 t.mem L.scr []) :
    WP isa (.call (Spec.Sha512.updateApi.name ++ v.suffix) (Impl.Sha512.X86_64.Stream.update v.callee)) t
      fun t' => Ctx L g mx m₀ t' ∧
        Spec.Sha512.Repr Spec.Sha512.H0_512 t'.mem L.scr (Spec.Ed25519.bytesAt m₀ L.seed 32) := by
  refine call_ok hL (upd_verified v).1 (upd_nosp v) (upd_depth v) hc (upd_pre hL hc ha) upd_sub upd_wsub
    fun s' hc' _ _ ⟨s₂, hm, _, hpost⟩ => ⟨hc', ?_⟩
  obtain ⟨hdi, hsi, hdx, hcx, -⟩ := upd_regs ha (updRd L) (updWr L)
  have h := hpost Spec.Sha512.H0_512 []
    (by rw [State.withRegions_mem, hdi]; exact hc.ce_repr hL hr) (by rw [hsi]; rfl)
  simp only [State.withRegions_mem, hdi, hdx, hcx, List.nil_append, hm] at h
  have e : Spec.Sha512.bytesAt t.callEntry.mem L.seed (BitVec.ofNat 64 32).toNat =
      Spec.Ed25519.bytesAt m₀ L.seed 32 := hc.ce_seed hL
  rwa [e] at h

theorem upd_step (v : Compress) (hL : L.Ok) {t : State} (hc : Ctx L g mx m₀ t)
    (hr : Spec.Sha512.Repr Spec.Sha512.H0_512 t.mem L.scr []) :
    WP isa (callWith pkUpdateArgs (Spec.Sha512.updateApi.name ++ v.suffix)
      (Impl.Sha512.X86_64.Stream.update v.callee)) t
      fun t' => Ctx L g mx m₀ t' ∧
        Spec.Sha512.Repr Spec.Sha512.H0_512 t'.mem L.scr (Spec.Ed25519.bytesAt m₀ L.seed 32) :=
  WP.seq (WP.mono (updArgs_ok hc) fun _ ⟨hc₁, hm₁, ha⟩ => upd_call v hL hc₁ ha (hm₁ ▸ hr))

/-- What the call of `finalize` needs of the registers. -/
def FinArgs (L : Lay) (t : State) : Prop :=
  t.gpr .rdi = L.scr ∧ t.gpr .rsi = BitVec.ofNat 64 32 ∧ t.gpr .rdx = L.scr + BitVec.ofNat 64 1568 ∧
    t.gpr .rcx = L.scr + BitVec.ofNat 64 192

theorem finArgs_ok {t : State} (hc : Ctx L g mx m₀ t) :
    WP isa (.block pkFinalizeArgs) t fun t' => Ctx L g mx m₀ t' ∧ t'.mem = t.mem ∧ FinArgs L t' := by
  have h48 := hc.inFr (d := 48) (by omega) (by omega)
  apply WP.of_runBlock
  simp only [pkFinalizeArgs, scrPtr, shaScratch, digestAt, fScratch, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, readSrc32, State.load64,
    State.setReg32, ea_stk, RegUpd.gpr_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg,
    RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags,
    Option.map_some, Option.bind_some, reduceCtorEq, ite_false, ite_true, hc.rsp, add_add,
    Nat.reduceAdd, h48, Option.some.injEq, exists_eq_left', hc.pScr, FinArgs]
  exact ⟨hc.regs rfl rfl rfl rfl (by cs_tac), trivial, trivial, rfl, by rw [sx32 (by omega)],
    by rw [sx32 (by omega)]⟩

theorem bytesAt_length (m : Mem) (p : Addr) (n : Nat) : (Spec.Ed25519.bytesAt m p n).length = n := by
  simp [Spec.Ed25519.bytesAt]

abbrev finRd : List Region := []
abbrev finWr (L : Lay) : List Region :=
  [⟨L.scr, 192⟩, ⟨L.scr + BitVec.ofNat 64 1568, 64⟩, ⟨L.scr + BitVec.ofNat 64 192, 1376⟩]

theorem fin_regs {t : State} (ha : FinArgs L t) (rd wr : List Region) :
    (t.callEntry.withRegions rd wr).gpr .rdi = L.scr ∧
      (t.callEntry.withRegions rd wr).gpr .rsi = BitVec.ofNat 64 32 ∧
      (t.callEntry.withRegions rd wr).gpr .rdx = L.scr + BitVec.ofNat 64 1568 ∧
      (t.callEntry.withRegions rd wr).gpr .rcx = L.scr + BitVec.ofNat 64 192 :=
  ⟨(gpr_ce _ _ _ (by decide)).trans ha.1, (gpr_ce _ _ _ (by decide)).trans ha.2.1,
    (gpr_ce _ _ _ (by decide)).trans ha.2.2.1, (gpr_ce _ _ _ (by decide)).trans ha.2.2.2⟩

theorem fin_pre (hL : L.Ok) {t : State} (hc : Ctx L g mx m₀ t) (ha : FinArgs L t) :
    Proof.Sha512.finalizeX86_64.pre (t.callEntry.withRegions finRd (finWr L)) := by
  obtain ⟨hdi, -, hdx, hcx⟩ := fin_regs ha finRd (finWr L)
  simp only [Proof.Sha512.finalizeX86_64, rsp_ce, hdi, hdx, hcx, hc.rsp, sub8, sub88,
    State.withRegions_rd, State.withRegions_wr]
  exact ⟨by first | trivial | rfl, by first | trivial | rfl, Offset.base_disjoint _ (by omega) (by omega),
    Offset.base_disjoint _ (by omega) (by omega), Offset.disjoint _ (by omega) (by omega) (by omega),
    by simpa using hL.stk_scr (d := 8) (n := 8) (e := 0) (k := 192) (by omega) (by omega),
    hL.stk_scr (d := 8) (n := 8) (by omega) (by omega),
    hL.stk_scr (d := 8) (n := 8) (by omega) (by omega),
    by simpa using hL.stk_scr (d := 0) (n := 8) (e := 0) (k := 192) (by omega) (by omega),
    by simpa using hL.stk_scr (d := 0) (n := 8) (e := 1568) (k := 64) (by omega) (by omega),
    by simpa using hL.stk_scr (d := 0) (n := 8) (e := 192) (k := 1376) (by omega) (by omega)⟩

theorem fin_sub : ∀ r ∈ finRd ++ finWr L, ∃ R ∈ [L.SEED, L.FR, L.OUT, L.SCR], Within r R := by
  simp only [List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact ⟨L.SCR, by simp, within_base _ (by omega)⟩
  · exact ⟨L.SCR, by simp, within_off _ (by omega)⟩
  · exact ⟨L.SCR, by simp, within_off _ (by omega)⟩

theorem fin_wsub : ∀ r ∈ finWr L, Within r L.OUT ∨ Within r L.SCR := by
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact .inr (within_base _ (by omega))
  · exact .inr (within_off _ (by omega))
  · exact .inr (within_off _ (by omega))

theorem fin_call (v : Compress) (hL : L.Ok) {t : State} (hc : Ctx L g mx m₀ t) (ha : FinArgs L t)
    (hr : Spec.Sha512.Repr Spec.Sha512.H0_512 t.mem L.scr (Spec.Ed25519.bytesAt m₀ L.seed 32)) :
    WP isa (.call (Spec.Sha512.finalizeApi.name ++ v.suffix) (Impl.Sha512.X86_64.Stream.finalize v.callee)) t
      fun t' => Ctx L g mx m₀ t' ∧ Spec.Sha512.bytesAt t'.mem (L.scr + BitVec.ofNat 64 1568) 64 =
        Spec.Sha512.sha512 (Spec.Ed25519.bytesAt m₀ L.seed 32) := by
  refine call_ok hL (fin_verified v).1 (fin_nosp v) (fin_depth v) hc (fin_pre hL hc ha) fin_sub fin_wsub
    fun s' hc' _ _ ⟨s₂, hm, _, hpost⟩ => ⟨hc', ?_⟩
  obtain ⟨hdi, hsi, hdx, -⟩ := fin_regs ha finRd (finWr L)
  have h := hpost Spec.Sha512.H0_512 (Spec.Ed25519.bytesAt m₀ L.seed 32)
    (by rw [State.withRegions_mem, hdi]; exact hc.ce_repr hL hr)
    (by rw [bytesAt_length]; decide) (by rw [hsi, bytesAt_length])
  rw [hdx, hm] at h
  exact h

theorem fin_step (v : Compress) (hL : L.Ok) {t : State} (hc : Ctx L g mx m₀ t)
    (hr : Spec.Sha512.Repr Spec.Sha512.H0_512 t.mem L.scr (Spec.Ed25519.bytesAt m₀ L.seed 32)) :
    WP isa (callWith pkFinalizeArgs (Spec.Sha512.finalizeApi.name ++ v.suffix)
      (Impl.Sha512.X86_64.Stream.finalize v.callee)) t
      fun t' => Ctx L g mx m₀ t' ∧ Spec.Sha512.bytesAt t'.mem (L.scr + BitVec.ofNat 64 1568) 64 =
        Spec.Sha512.sha512 (Spec.Ed25519.bytesAt m₀ L.seed 32) :=
  WP.seq (WP.mono (finArgs_ok hc) fun _ ⟨hc₁, hm₁, ha⟩ => fin_call v hL hc₁ ha (hm₁ ▸ hr))

end VG.Proof.Ed25519.X86_64.PublicKey




