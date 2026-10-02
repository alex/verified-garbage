import VerifiedGarbage.Proof.MdStream.AArch64.Common
import VerifiedGarbage.Proof.Sha256.AArch64.Compress
import VerifiedGarbage.Proof.Sha256.Stream
import VerifiedGarbage.Impl.Sha256.AArch64.Stream
import VerifiedGarbage.Proof.Sha256.AArch64.Lit

/-!
# SHA-256 on AArch64: calling the compression function

The call of the compression function (`compressAt`), as HMAC-SHA-256 and
PBKDF2-HMAC-SHA-256 use it. The weakest-precondition rules it is proved
with are the generic ones (`VG.Proof.MdStream.AArch64`).
-/

namespace VG.Proof.Sha256.AArch64.Stream

open VG VG.AArch64 VG.Impl.Sha256.AArch64.Stream
open VG.Proof.Sha256.AArch64 (compress_verified)
open VG.Proof.MdStream.AArch64 (Upd wp_mov wp_movz one_toNat)
open VG.Spec.Sha256 (HashValue stateAt blockAt compressBlocks compress)

/-! ## The compression function -/

theorem compressBlocks_one (H : HashValue) (m : Mem) (p : Addr) :
    compressBlocks H m p 1 = compress H (blockAt m p) := by
  simp [compressBlocks]

theorem compress_noFrames : Impl.Sha256.AArch64.compress.noFrames = true := by lit_decide

/-- Compressing the block at `x1` into the hash value at `x19`, with scratch
space at `x20`: the callee-saved registers other than `x30` are kept. -/
theorem compressAt_ok {s : State} {st scr src : Addr}
    (h19 : s.gpr .x19 = st) (h20 : s.gpr .x20 = scr) (h1 : s.gpr .x1 = src)
    (d₁ : Region.Disjoint ⟨st, 32⟩ ⟨scr, 112⟩) (d₂ : Region.Disjoint ⟨src, 64⟩ ⟨st, 32⟩)
    (d₃ : Region.Disjoint ⟨src, 64⟩ ⟨scr, 112⟩)
    (hc : Covers [⟨src, 64⟩, ⟨st, 32⟩, ⟨scr, 112⟩] (s.rd ++ s.wr))
    (hw : Covers [⟨st, 32⟩, ⟨scr, 112⟩] s.wr) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s.gpr r) →
      s'.sp = s.sp → Frame [⟨st, 32⟩, ⟨scr, 112⟩] s.mem s'.mem →
      stateAt s'.mem st = compress (stateAt s.mem st) (blockAt s.mem src) → Q s') :
    WP isa compressAt s Q := by
  unfold compressAt
  refine WP.seq (wp_mov fun s₁ u₁ => wp_movz fun s₂ u₂ => wp_mov fun s₃ u₃ => WP.block_nil ?_)
  have e0 : s₃.gpr .x0 = st := by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, h19]
  have e1 : s₃.gpr .x1 = src := by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h1]
  have e2 : s₃.gpr .x2 = BitVec.setWidth 64 (1 : BitVec 16) := by
    rw [u₃.other _ (by decide), u₂.gpr]
  have e3 : s₃.gpr .x3 = scr := by
    rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), h20]
  have keep : ∀ r ∈ preserved, s₃.gpr r = s.gpr r := by
    intro r hr
    have : r ≠ .x0 ∧ r ≠ .x2 ∧ r ≠ .x3 := by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        decide
    rw [u₃.other _ this.2.2, u₂.other _ this.2.1, u₁.other _ this.1]
  have m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  have rd₃ : s₃.rd = s.rd := by rw [u₃.rd, u₂.rd, u₁.rd]
  have wr₃ : s₃.wr = s.wr := by rw [u₃.wr, u₂.wr, u₁.wr]
  have sp₃ : s₃.sp = s.sp := by rw [u₃.sp, u₂.sp, u₁.sp]
  have c0 : s₃.callEntry.gpr .x0 = st := (State.callEntry_gpr _ (by decide)).trans e0
  have c1 : s₃.callEntry.gpr .x1 = src := (State.callEntry_gpr _ (by decide)).trans e1
  have c2 : s₃.callEntry.gpr .x2 = BitVec.setWidth 64 (1 : BitVec 16) :=
    (State.callEntry_gpr _ (by decide)).trans e2
  have c3 : s₃.callEntry.gpr .x3 = scr := (State.callEntry_gpr _ (by decide)).trans e3
  refine WP.call (k := Proof.Sha256.compressAArch64) compress_verified.1
    (rd := [⟨src, 64 * 1⟩]) (wr := [⟨st, 32⟩, ⟨scr, 112⟩]) ?_ ?_ ?_ ?_ compress_noFrames
  · simp only [Proof.Sha256.compressAArch64, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, c0, c1, c2, c3, one_toNat]
    exact ⟨trivial, trivial, d₁, d₂, d₃⟩
  · rw [rd₃, wr₃]; simpa using hc
  · rw [wr₃]; exact hw
  · intro s' hrd hwr hsp hf hcs _ hpost
    simp only [Proof.Sha256.compressAArch64, State.withRegions_gpr, State.withRegions_mem,
      State.callEntry_mem, c0, c1, c2, one_toNat, compressBlocks_one, m₃] at hpost
    exact hQ s' (hrd.trans rd₃) (hwr.trans wr₃) (fun r hr h30 => (hcs r hr h30).trans (keep r hr))
      (hsp.trans sp₃) (m₃ ▸ hf) hpost

end VG.Proof.Sha256.AArch64.Stream
