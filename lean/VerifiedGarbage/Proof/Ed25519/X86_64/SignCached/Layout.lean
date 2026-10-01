import VerifiedGarbage.Impl.Ed25519.X86_64.SignCached
import VerifiedGarbage.Proof.Ed25519.X86_64.PublicKey.Hash

/-! The frame and memory invariant of complete Ed25519 signing. -/
namespace VG.Proof.Ed25519.X86_64.SignCached

open VG VG.X86_64
open VG.Proof.Ed25519.X86_64.PublicKey (Within within_base within_off)

structure Lay where
  out : Addr
  seed : Addr
  pk : Addr
  msg : Addr
  len : BitVec 64
  scr : Addr
  B : Addr

namespace Lay
variable (L : Lay)
abbrev OUT : Region := ⟨L.out, 64⟩
abbrev SEED : Region := ⟨L.seed, 32⟩
abbrev PK : Region := ⟨L.pk, 32⟩
abbrev MSG : Region := ⟨L.msg, L.len.toNat⟩
abbrev SCR : Region := ⟨L.scr, 8192⟩
abbrev STK : Region := ⟨L.B, 264⟩
abbrev FR : Region := ⟨L.B + BitVec.ofNat 64 16, 248⟩
abbrev DATA : Region := ⟨L.B + BitVec.ofNat 64 16, 192⟩
abbrev RET : Region := ⟨L.B + BitVec.ofNat 64 264, 8⟩
def inputs : List Region := [L.SEED, L.PK, L.MSG]
structure Ok : Prop where
  os : ∀ r ∈ L.inputs, L.OUT.Disjoint r
  oc : L.OUT.Disjoint L.SCR
  ko : L.STK.Disjoint L.OUT
  ro : L.RET.Disjoint L.OUT
  no : L.out.toNat + 64 ≤ 2 ^ 64
  sc : ∀ r ∈ L.inputs, r.Disjoint L.SCR
  ks : ∀ r ∈ L.inputs, L.STK.Disjoint r
  rs : ∀ r ∈ L.inputs, L.RET.Disjoint r
  kc : L.STK.Disjoint L.SCR
  rc : L.RET.Disjoint L.SCR
  np : L.pk.toNat + 32 ≤ 2 ^ 64
  nm : L.msg.toNat + L.len.toNat ≤ 2 ^ 64
  ns : L.seed.toNat + 32 ≤ 2 ^ 64
  nc : L.scr.toNat + 8192 ≤ 2 ^ 64
end Lay

namespace Lay.Ok
variable {L : Lay}
theorem stk_scr (h : L.Ok) {d n e k : Nat} (h₁ : d + n ≤ 264) (h₂ : e + k ≤ 8192) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ ⟨L.scr + BitVec.ofNat 64 e, k⟩ :=
  (h.kc.sub_left (Offset.sub_base _ h₁)).sub_right (Offset.sub_base _ h₂)
theorem stk_input (h : L.Ok) {r : Region} (hr : r ∈ L.inputs) {d n : Nat} (hd : d + n ≤ 264) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ r :=
  (h.ks r hr).sub_left (Offset.sub_base _ hd)
theorem input_scr (h : L.Ok) {r : Region} (hr : r ∈ L.inputs) {e k : Nat} (he : e + k ≤ 8192) :
    Region.Disjoint r ⟨L.scr + BitVec.ofNat 64 e, k⟩ :=
  (h.sc r hr).sub_right (Offset.sub_base _ he)
end Lay.Ok

structure Ctx (L : Lay) (g : Reg → BitVec 64) (mx : BitVec 32) (m₀ : Mem) (t : State) : Prop where
  rd : t.rd = L.inputs
  wr : t.wr = [L.FR, L.OUT, L.SCR]
  rsp : t.gpr .rsp = L.B + BitVec.ofNat 64 16
  cs : ∀ r ∈ calleeSaved, r ≠ .rsp → t.gpr r = g r
  mx : t.mxcsr.extractLsb' 6 10 = mx.extractLsb' 6 10
  pScr : t.mem.readW (L.B + BitVec.ofNat 64 216) 64 = L.scr
  pLen : t.mem.readW (L.B + BitVec.ofNat 64 224) 64 = L.len
  pMsg : t.mem.readW (L.B + BitVec.ofNat 64 232) 64 = L.msg
  pPk : t.mem.readW (L.B + BitVec.ofNat 64 240) 64 = L.pk
  pSeed : t.mem.readW (L.B + BitVec.ofNat 64 248) 64 = L.seed
  pOut : t.mem.readW (L.B + BitVec.ofNat 64 256) 64 = L.out
  frame : Frame [L.OUT, L.SCR, L.STK] m₀ t.mem

namespace Ctx
variable {L : Lay} {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem} {t t' : State}
theorem regs (hc : Ctx L g mx m₀ t) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) (hm : t'.mem = t.mem)
    (hmx : t'.mxcsr = t.mxcsr) (hg : ∀ r ∈ calleeSaved, t'.gpr r = t.gpr r) : Ctx L g mx m₀ t' :=
  ⟨hrd.trans hc.rd, hwr.trans hc.wr, (hg .rsp (by decide)).trans hc.rsp,
    fun r hr hr' => (hg r hr).trans (hc.cs r hr hr'), by rw [hmx]; exact hc.mx,
    by rw [hm]; exact hc.pScr, by rw [hm]; exact hc.pLen,
    by rw [hm]; exact hc.pMsg, by rw [hm]; exact hc.pPk,
    by rw [hm]; exact hc.pSeed, by rw [hm]; exact hc.pOut, by rw [hm]; exact hc.frame⟩
theorem ret (hc : Ctx L g mx m₀ t) : below (t.gpr .rsp) 8 = ⟨L.B + BitVec.ofNat 64 8, 8⟩ := by
  rw [hc.rsp]
  show (⟨L.B + BitVec.ofNat 64 16 - BitVec.ofNat 64 8, 8⟩ : Region) = _
  rw [PublicKey.sub8']
theorem inFr (hc : Ctx L g mx m₀ t) {d : Nat} (h₁ : 16 ≤ d) (h₂ : d + 8 ≤ 264) :
    InRegions (t.rd ++ t.wr) (L.B + BitVec.ofNat 64 d) 8 :=
  ⟨L.FR, by rw [hc.rd, hc.wr]; simp, Offset.contains _ h₁ (by omega) (by omega)⟩
theorem inFrW (hc : Ctx L g mx m₀ t) {d : Nat} (h₁ : 16 ≤ d) (h₂ : d + 8 ≤ 264) :
    InRegions t.wr (L.B + BitVec.ofNat 64 d) 8 :=
  ⟨L.FR, by rw [hc.wr]; simp, Offset.contains _ h₁ (by omega) (by omega)⟩
theorem ea_fr (hc : Ctx L g mx m₀ t) (d : Nat) :
    t.ea (Impl.Ed25519.X86_64.stk d) = L.B + BitVec.ofNat 64 (16 + d) := by
  rw [PublicKey.ea_stk, hc.rsp, PublicKey.add_add]
theorem input_byte (hL : L.Ok) (hc : Ctx L g mx m₀ t) {r : Region} (hr : r ∈ L.inputs)
    (hn : r.len ≤ 2 ^ 64) {i : Nat} (hi : i < r.len) :
    t.mem (r.base + BitVec.ofNat 64 i) = m₀ (r.base + BitVec.ofNat 64 i) :=
  Frame.bytes hc.frame (by
    intro R hR
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl | rfl
    · exact (hL.os r hr).symm
    · exact hL.sc r hr
    · exact (hL.ks r hr).symm) hn hi
end Ctx

/-- Calls may overwrite scratch, output and frame data, but not the saved arguments. -/
theorem call_ok {L : Lay} (hL : L.Ok) {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem}
    {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hsp : NoSp c) (hd : c.depth ≤ 1) {t : State} (hc : Ctx L g mx m₀ t)
    {rd wr : List Region} (hpre : k.pre (t.callEntry.withRegions rd wr))
    (hsub : ∀ r ∈ rd ++ wr, ∃ R ∈ L.inputs ++ [L.FR, L.OUT, L.SCR], Within r R)
    (hwsub : ∀ r ∈ wr, Within r L.DATA ∨ Within r L.OUT ∨ Within r L.SCR) {Q : State → Prop}
    (hQ : ∀ s', Ctx L g mx m₀ s' → Frame (wr ++ [⟨L.B, 16⟩]) t.mem s'.mem →
      (∀ r, (∀ i ∈ instrs c, Taint.clobbers i r = false) → s'.gpr r = t.gpr r) →
      (∃ s₂ : State, s₂.mem = s'.mem ∧ (∀ r, r ≠ .rsp → s₂.gpr r = s'.gpr r) ∧
        k.post (t.callEntry.withRegions rd wr) s₂) → Q s') :
    WP isa (.call n c) t Q := by
  have hcov : Covers (rd ++ wr) (t.rd ++ t.wr) := by
    refine Covers.of_sub fun r hr => ?_
    obtain ⟨R, hR, hw⟩ := hsub r hr
    exact ⟨R, by rw [hc.rd, hc.wr]; exact hR, hw⟩
  have hcovw : Covers wr t.wr := by
    refine Covers.of_sub fun r hr => ?_
    rw [hc.wr]
    rcases hwsub r hr with h | h | h
    · obtain ⟨off, hb, hn⟩ := h
      exact ⟨L.FR, by simp, off, hb, by exact Nat.le_trans hn (by show 192 ≤ 248; decide)⟩
    · exact ⟨L.OUT, by simp, h⟩
    · exact ⟨L.SCR, by simp, h⟩
  refine WP.call_mx hv hsp (by omega) hpre hcov hcovw fun s' hrd hwr hcs hf hg hpost hmx => ?_
  have hf' : Frame (wr ++ [⟨L.B, 16⟩]) t.mem s'.mem := by
    refine Frame.sub hf fun r hr => ?_
    rcases List.mem_append.mp hr with hr | hr
    · exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
    · simp only [List.mem_singleton] at hr; subst hr
      refine ⟨_, List.mem_append_right _ (List.mem_singleton_self _), ?_⟩
      rw [hc.rsp]
      exact PublicKey.below_call_sub _ (by omega)
  have hdisj : ∀ d, 216 ≤ d → d + 8 ≤ 264 → ∀ r ∈ wr ++ [⟨L.B, 16⟩],
      Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, 8⟩ r := by
    intro d h₁ h₂ r hr
    rcases List.mem_append.mp hr with hr | hr
    · rcases hwsub r hr with h | h | h
      · exact (Offset.disjoint L.B (d := d) (n := 8) (e := 16) (k := 192)
          (by omega) (by omega) (by omega)).sub_right h.sub
      · exact (hL.ko.sub_left (Offset.sub_base _ (by omega))).sub_right h.sub
      · exact (hL.kc.sub_left (Offset.sub_base _ (by omega))).sub_right h.sub
    · simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint_base _ (by omega) (by omega)
  have keep : ∀ d, 216 ≤ d → d + 8 ≤ 264 →
      s'.mem.readW (L.B + BitVec.ofNat 64 d) 64 = t.mem.readW (L.B + BitVec.ofNat 64 d) 64 :=
    fun d h₁ h₂ => hf'.readW (Region.contains_self _ _) (hdisj d h₁ h₂) (by decide)
  refine hQ s' ⟨hrd.trans hc.rd, hwr.trans hc.wr, ?_, fun r hr hr' => (hcs r hr).trans (hc.cs r hr hr'),
    hmx.trans hc.mx, (keep 216 (by omega) (by omega)).trans hc.pScr,
    (keep 224 (by omega) (by omega)).trans hc.pLen, (keep 232 (by omega) (by omega)).trans hc.pMsg,
    (keep 240 (by omega) (by omega)).trans hc.pPk, (keep 248 (by omega) (by omega)).trans hc.pSeed,
    (keep 256 (by omega) (by omega)).trans hc.pOut,
    hc.frame.trans (Frame.sub hf' fun r hr => ?_)⟩ hf' hg hpost
  · rw [hcs .rsp (by simp [calleeSaved]), hc.rsp]
  · rcases List.mem_append.mp hr with hr | hr
    · rcases hwsub r hr with h | h | h
      · exact ⟨L.STK, by simp, fun a ha => Offset.sub_base L.B (by decide : 16 + 192 ≤ 264) a (h.sub a ha)⟩
      · exact ⟨L.OUT, by simp, h.sub⟩
      · exact ⟨L.SCR, by simp, h.sub⟩
    · simp only [List.mem_singleton] at hr; subst hr
      refine ⟨L.STK, by simp, ?_⟩
      have := Offset.sub_base L.B (d := 0) (n := 16) (k := 264) (by omega)
      simpa using this

end VG.Proof.Ed25519.X86_64.SignCached
