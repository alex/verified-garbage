import VerifiedGarbage.Impl.Ed25519.X86_64.PointBatch
import VerifiedGarbage.Proof.Ed25519.X86_64.PointAccumulateLoop
import VerifiedGarbage.Proof.Ed25519.X86_64.PointPowersLoop

/-! The local table preserves the accumulator, bits, and checkpoints. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (Keeps clob)

variable {fld : Arith} [EdArith fld]

theorem PowersKeep.of_keep {base : Addr} {o n : Nat} {s t : State} (h : Keep base s t) :
    PowersKeep base o n s t := ⟨fun r _ _ hr => h.gpr r hr, h.rd, h.wr, TableFrame.workspace h.mem⟩

theorem loadCheckpoint_ok {s : State} {base : Addr} (hs : Scratch s base)
    (j : Nat) (hj : j < 32) (hc : s.gpr .rbx = BitVec.ofNat 64 j) :
    WP isa (.block (loadCheckpoint fld)) s fun t => Keep base s t ∧
      point (env t.mem base) 0 1 2 3 = tablePoint s.mem base (1280 + 128 * j) ∧
      point (env t.mem base) 17 18 19 20 = point (env s.mem base) 0 1 2 3 ∧
      env t.mem base 16 = env s.mem base 16 := by
  rw [loadCheckpoint, List.append_assoc, WP.block_append_iff]
  refine WP.mono (fieldCodeWide_ok hs savePointOps) fun a ⟨ka, va⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (tableAddr_ok (hs.of_keep ka).rdi 1280 j (by omega)
    ((ka.gpr _ (by decide)).trans hc)) fun b ⟨pb, kb⟩ => ?_
  have kbe : Keep base a b := Keep.of_keeps kb (by decide)
  refine WP.mono (pointFromTable_ok (hs.of_keep (ka.trans kbe)) pb (by omega) (by omega))
    fun t ⟨pt, kt⟩ => ?_
  refine ⟨(ka.trans kbe).trans (Keep.of_table kt), ?_, ?_, ?_⟩
  · rw [pt, kb.2.1]; exact workspace_tablePoint ka.mem (by omega) (by omega)
  · rw [savedPoint_congr _ _ (fun i hi => tableLoad_high kt i (by omega)), kb.2.1, va, savePoint_eval]
  · rw [tableLoad_high kt 16 (by decide), kb.2.1, va]; rfl

theorem prepareBatch_ok {s : State} {base : Addr} (hs : Scratch s base)
    (j : Nat) (hj : j < 32) (hc : s.gpr .rbx = BitVec.ofNat 64 j)
    (hd : env s.mem base 16 = Spec.Ed25519.d) :
    WP isa (prepareBatch fld) s fun t => PowersKeep base 5376 2048 s t ∧
      point (env t.mem base) 0 1 2 3 = point (env s.mem base) 0 1 2 3 ∧
      (∀ i < 16, tablePoint t.mem base (5376 + 128 * i) =
        powerPoint (tablePoint s.mem base (1280 + 128 * j)) i) ∧
      env t.mem base 16 = Spec.Ed25519.d := by
  rw [prepareBatch]
  refine WP.seq (WP.mono (loadCheckpoint_ok hs j hj hc) fun a ⟨ka, ap, av, ad⟩ => ?_)
  refine WP.seq (WP.mono (pointPowers_ok false (hs.of_keep ka) 5376 16 (by decide)
    (by decide) (by decide) (by decide) (ad.trans hd)) fun b ⟨bt, _, bh, kb⟩ => ?_)
  refine WP.mono (fieldCodeWide_ok (kb.scratch (hs.of_keep ka)) restorePointOps) fun t ⟨kt, vt⟩ => ?_
  refine ⟨((PowersKeep.of_keep ka).trans kb).trans (PowersKeep.of_keep kt), ?_, ?_, ?_⟩
  · rw [vt, restorePoint_eval, savedPoint_congr _ _ bh, av]
  · intro i hi
    rw [workspace_tablePoint kt.mem (by omega) (by omega), bt i hi, ap]
    simp only [powerStride, Bool.false_eq_true, ite_false, Nat.one_mul]
  · rw [vt]
    change env b.mem base 16 = _
    rw [bh 16 (by decide), ad, hd]

end VG.Proof.Ed25519.X86_64
