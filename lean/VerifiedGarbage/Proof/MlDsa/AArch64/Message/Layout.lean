import VerifiedGarbage.Impl.MlDsa.AArch64.Message
import VerifiedGarbage.Proof.MlKem.AArch64.KeccakCall
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.MlDsa.Message.Common

/-!
# ML-DSA on AArch64, `sign_message` and `verify_message`: where everything is

Untrusted: everything here is checked by Lean. The function's buffers, the
16 bytes of stack below the stack pointer on entry (`STK`, which the calls'
frames use), and the 1 KiB `X` of `scratch` after the working space of the
function on `μ` (`Lay`): the Keccak state, the sponge functions' working
space and `μ` in its first 904 bytes (`W`), then the saved registers and
arguments and the two bytes of the formatted message (`SV`). `Ctx` is what
holds from the entry's saves to the exit: the permissions, the stack
pointer, `x28` pointing at `X`, the callee-saved registers, the saves, and
that memory changed only in `X` and `STK`. `Ctx.keep` carries it over code
that writes only within `W` and `STK`.
-/

namespace VG.Proof.MlDsa.AArch64.Message

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Message
open VG.Proof.MlDsa.Message
open VG.Spec.Sha3 (bytesAt)

theorem covers_of_within {rs rs' : List Region} (h : ∀ r ∈ rs, ∃ R ∈ rs', Within r R) : Covers rs rs' :=
  Covers.of_sub fun r hr => by
    obtain ⟨R, hR, o, hb, hl⟩ := h r hr
    exact ⟨R, hR, o, hb, hl⟩

/-! ## The layout -/

/-- The stack pointer on entry, the buffers, the offset `E` of the 1 KiB `X`
in `scratch`, and the permissions on entry. -/
structure Lay where
  SP : Addr
  key : Addr
  keyLen : Nat
  msg : Addr
  len : BitVec 64
  ctx : Addr
  ctxLen : BitVec 64
  rnd : Addr
  sig : Addr
  scr : Addr
  E : Nat
  rd : List Region
  wr : List Region

namespace Lay

variable (L : Lay)

/-- The 16 bytes of stack the calls' frames use. -/
abbrev STK : Region := below L.SP 16
/-- The 1 KiB. -/
abbrev X : Addr := L.scr + BitVec.ofNat 64 L.E
abbrev XS : Region := ⟨L.X, 1024⟩
/-- What the calls write in it: the Keccak state, the sponge functions'
working space and `μ`. -/
abbrev W : Region := ⟨L.X, 904⟩
/-- The saves and the two bytes of the formatted message. -/
abbrev SV : Region := ⟨L.X + BitVec.ofNat 64 904, 88⟩
abbrev ST : Addr := L.X
abbrev KS : Addr := L.X + BitVec.ofNat 64 200
abbrev MU : Addr := L.X + BitVec.ofNat 64 840
abbrev KEY : Region := ⟨L.key, L.keyLen⟩
abbrev MSG : Region := ⟨L.msg, L.len.toNat⟩
abbrev CTX : Region := ⟨L.ctx, L.ctxLen.toNat⟩

/-- The saved arguments, at `X + 920 + 8j`. -/
def vals : List (BitVec 64) := [L.key, L.msg, L.len, L.ctx, L.ctxLen, L.rnd, L.sig, L.scr]

/-- What the contract says of where everything is. -/
structure Ok : Prop where
  ctxLt : L.ctxLen.toNat < 256
  hE : L.E + 1024 < 2 ^ 31
  hKey : 128 ≤ L.keyLen ∧ L.keyLen < 2 ^ 16
  nSP : 16 ≤ L.SP.toNat
  nX : L.X.toNat + 1024 ≤ 2 ^ 64
  inX : ∃ R ∈ L.wr, Within L.XS R
  inKey : L.KEY ∈ L.rd
  inMsg : L.MSG ∈ L.rd
  inCtx : L.CTX ∈ L.rd
  xKey : L.XS.Disjoint L.KEY
  xMsg : L.XS.Disjoint L.MSG
  xCtx : L.XS.Disjoint L.CTX
  kX : L.STK.Disjoint L.XS
  kKey : L.STK.Disjoint L.KEY
  kMsg : L.STK.Disjoint L.MSG
  kCtx : L.STK.Disjoint L.CTX
  nKey : L.key.toNat + L.keyLen ≤ 2 ^ 64
  nMsg : L.msg.toNat + L.len.toNat ≤ 2 ^ 64
  nCtx : L.ctx.toNat + L.ctxLen.toNat ≤ 2 ^ 64
  lenW : ∀ R ∈ L.wr, R.len ≤ 2 ^ 64

end Lay

namespace Lay.Ok

variable {L : Lay}

theorem stk_x (h : L.Ok) {e k : Nat} (h₂ : e + k ≤ 1024) :
    Region.Disjoint L.STK ⟨L.X + BitVec.ofNat 64 e, k⟩ :=
  h.kX.sub_right (Offset.sub_base _ h₂)

theorem x_r (_h : L.Ok) {r : Region} (hr : L.XS.Disjoint r) {e k : Nat} (h₂ : e + k ≤ 1024) :
    Region.Disjoint ⟨L.X + BitVec.ofNat 64 e, k⟩ r :=
  hr.sub_left (Offset.sub_base _ h₂)

/-- The 1 KiB is writable. -/
theorem covX (h : L.Ok) {e k : Nat} (h₂ : e + k ≤ 1024) : ∃ R ∈ L.wr, Within ⟨L.X + BitVec.ofNat 64 e, k⟩ R := by
  obtain ⟨R, hR, hw⟩ := h.inX
  exact ⟨R, hR, (within_off L.X h₂).trans hw⟩

/-- Bytes of the 1 KiB are writable. -/
theorem inW (h : L.Ok) {e k : Nat} (h₂ : e + k ≤ 1024) (hk : 0 < k) : InRegions L.wr (L.X + BitVec.ofNat 64 e) k := by
  obtain ⟨R, hR, o, hb, hl⟩ := h.covX h₂
  refine ⟨R, hR, ?_⟩
  simp only at hb hl
  rw [hb]
  exact Offset.contains_base _ hl (by have := h.lenW R hR; omega)

/-- What lies within the first 904 bytes of `X`, or in `STK`, is apart from the saves. -/
theorem sv_disj (h : L.Ok) {r : Region} (hr : Within r L.W ∨ Region.Sub r L.STK) {d n : Nat} (hd : d + n ≤ 88) :
    Region.Disjoint ⟨L.X + BitVec.ofNat 64 904 + BitVec.ofNat 64 d, n⟩ r := by
  rw [add_add]
  rcases hr with hr | hr
  · obtain ⟨o, hb, hl⟩ := hr
    obtain ⟨b, k⟩ := r
    simp only at hb hl
    subst hb
    exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)
  · exact (h.kX.symm.sub_left (Offset.sub_base _ (by omega))).sub_right hr

end Lay.Ok

/-! ## From the entry's saves to the exit -/

/-- The state from the entry's saves to the exit: `g` and `v` are the
registers on entry, `m₀` the memory. -/
structure Ctx (L : Lay) (g : Reg → BitVec 64) (v : VReg → BitVec 128) (m₀ : Mem) (t : State) : Prop where
  rd : t.rd = L.rd
  wr : t.wr = L.wr
  sp : t.sp = L.SP
  x28 : t.gpr .x28 = L.X
  cs : ∀ r ∈ preserved, r ≠ .x28 → r ≠ .x30 → t.gpr r = g r
  vs : ∀ r ∈ preservedV, (t.v r).extractLsb' 0 64 = (v r).extractLsb' 0 64
  s28 : t.mem.readW (L.X + BitVec.ofNat 64 904 + BitVec.ofNat 64 0) 64 = g .x28
  s30 : t.mem.readW (L.X + BitVec.ofNat 64 904 + BitVec.ofNat 64 8) 64 = g .x30
  slot : ∀ j < 8, t.mem.readW (L.X + BitVec.ofNat 64 904 + BitVec.ofNat 64 (16 + 8 * j)) 64 = L.vals.getD j 0
  hdr : bytesAt t.mem (L.X + BitVec.ofNat 64 904 + BitVec.ofNat 64 80) 2 = [0, BitVec.ofNat 8 L.ctxLen.toNat]
  frame : Frame [L.XS, L.STK] m₀ t.mem

namespace Ctx

variable {L : Lay} {g : Reg → BitVec 64} {v : VReg → BitVec 128} {m₀ : Mem} {t t' : State}

/-- Code that writes only registers but `x28` and the callee-saved ones. -/
theorem regs (hc : Ctx L g v m₀ t) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) (hsp : t'.sp = t.sp)
    (hm : t'.mem = t.mem) (hvs : ∀ r ∈ preservedV, (t'.v r).extractLsb' 0 64 = (t.v r).extractLsb' 0 64)
    (hg : ∀ r ∈ preserved, r ≠ .x30 → t'.gpr r = t.gpr r) : Ctx L g v m₀ t' :=
  ⟨hrd.trans hc.rd, hwr.trans hc.wr, hsp.trans hc.sp, (hg .x28 (by decide) (by decide)).trans hc.x28,
    fun r hr h28 h30 => (hg r hr h30).trans (hc.cs r hr h28 h30), fun r hr => (hvs r hr).trans (hc.vs r hr),
    by rw [hm]; exact hc.s28, by rw [hm]; exact hc.s30, fun j hj => by rw [hm]; exact hc.slot j hj,
    by rw [hm]; exact hc.hdr, by rw [hm]; exact hc.frame⟩

/-- Code that writes memory only within the first 904 bytes of `X` and in `STK`. -/
theorem keep (hc : Ctx L g v m₀ t) (hL : L.Ok) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) (hsp : t'.sp = t.sp)
    (hvs : ∀ r ∈ preservedV, (t'.v r).extractLsb' 0 64 = (t.v r).extractLsb' 0 64)
    (hg : ∀ r ∈ preserved, r ≠ .x30 → t'.gpr r = t.gpr r) {rs : List Region} (hf : Frame rs t.mem t'.mem)
    (hrs : ∀ r ∈ rs, Within r L.W ∨ Region.Sub r L.STK) : Ctx L g v m₀ t' := by
  have keep : ∀ d, d + 8 ≤ 88 → t'.mem.readW (L.X + BitVec.ofNat 64 904 + BitVec.ofNat 64 d) 64 =
      t.mem.readW (L.X + BitVec.ofNat 64 904 + BitVec.ofNat 64 d) 64 :=
    fun d h => hf.readW (Region.contains_self _ _) (fun r hr => hL.sv_disj (hrs r hr) h) (by decide)
  have khdr : bytesAt t'.mem (L.X + BitVec.ofNat 64 904 + BitVec.ofNat 64 80) 2 =
      bytesAt t.mem (L.X + BitVec.ofNat 64 904 + BitVec.ofNat 64 80) 2 :=
    Proof.MlKem.bytesAt_congr fun i hi =>
      hf.bytes (R := ⟨_, 2⟩) (fun r hr => hL.sv_disj (hrs r hr) (by decide)) (by show 2 ≤ 2 ^ 64; decide) hi
  refine ⟨hrd.trans hc.rd, hwr.trans hc.wr, hsp.trans hc.sp, (hg .x28 (by decide) (by decide)).trans hc.x28,
    fun r hr h28 h30 => (hg r hr h30).trans (hc.cs r hr h28 h30), fun r hr => (hvs r hr).trans (hc.vs r hr),
    (keep 0 (by decide)).trans hc.s28, (keep 8 (by decide)).trans hc.s30,
    fun j hj => (keep _ (by omega)).trans (hc.slot j hj), khdr.trans hc.hdr,
    hc.frame.trans (Frame.sub hf fun r hr => ?_)⟩
  rcases hrs r hr with h | h
  · exact ⟨L.XS, by simp, (h.trans (within_base L.X (by decide : 904 ≤ 1024))).sub⟩
  · exact ⟨L.STK, by simp, h⟩

/-- A byte of a region apart from `X` and `STK`, as on entry. -/
theorem bytesAt_eq (hc : Ctx L g v m₀ t) {p : Addr} {n : Nat} (hx : L.XS.Disjoint ⟨p, n⟩)
    (hk : L.STK.Disjoint ⟨p, n⟩) (hn : n ≤ 2 ^ 64) : bytesAt t.mem p n = bytesAt m₀ p n :=
  Proof.MlKem.bytesAt_congr fun _ hi => Frame.bytes (R := ⟨p, n⟩) hc.frame (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hx.symm
    · exact hk.symm) hn hi

/-- Bytes of `X` are readable. -/
theorem inX (hc : Ctx L g v m₀ t) (hL : L.Ok) {e k : Nat} (h₂ : e + k ≤ 1024) (hk : 0 < k) :
    InRegions (t.rd ++ t.wr) (L.X + BitVec.ofNat 64 e) k := by
  obtain ⟨R, hR, hc'⟩ := hL.inW h₂ hk
  exact ⟨R, by rw [hc.rd, hc.wr]; exact List.mem_append_right _ hR, hc'⟩

end Ctx

end VG.Proof.MlDsa.AArch64.Message
