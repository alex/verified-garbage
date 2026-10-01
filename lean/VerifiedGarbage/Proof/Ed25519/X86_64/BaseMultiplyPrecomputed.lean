import VerifiedGarbage.Proof.Ed25519.X86_64.BaseCheckpointStore
import VerifiedGarbage.Proof.Ed25519.X86_64.PointMul

namespace VG.Proof.Ed25519.X86_64
open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (off ofs)

theorem baseMultiplyPrecomputedInit_ok {s : State} {base : Addr} (hs : Scratch s base)
    (scalar : Nat) (hscalar : scalar < 2 ^ (16 * 16))
    (hd : env s.mem base 16 = Spec.Ed25519.d)
    (hb : ∀ i < 16 * 16, s.mem (off base (768 + i)) = BitVec.ofNat 8 ((scalar / 2 ^ i) % 2)) :
    WP isa baseMultiplyPrecomputedInit s fun t =>
      PointMulInv s base 16 scalar Spec.Ed25519.basePoint 16 t := by
  rw [baseMultiplyPrecomputedInit]
  refine WP.seq (WP.mono (baseCheckpointStores_ok hs 16 (by decide))
    fun a ⟨ka, atab, ahigh⟩ => ?_)
  have ad : env a.mem base 16 = Spec.Ed25519.d := ahigh.trans hd
  have abits : ∀ i < 16 * 16, a.mem (off base (768 + i)) = BitVec.ofNat 8 ((scalar / 2 ^ i) % 2) := by
    intro i hi
    rw [ka.mem _ (by rw [Proof.X25519.X86_64.ofs_off' base (by omega)]; omega)
      (by rw [Proof.X25519.X86_64.ofs_off' base (by omega)]; omega), hb i hi]
  have kat : PowersKeep base 56 7368 s a := ka.mono (by decide) (by omega)
  refine WP.seq (WP.mono (fieldCodeWide_ok (ka.scratch hs) (constPointOps Spec.Ed25519.identity))
    fun b ⟨kb, vb⟩ => ?_)
  have bd : env b.mem base 16 = Spec.Ed25519.d := by rw [vb]; exact ad
  have bp : point (env b.mem base) 0 1 2 3 =
      after scalar Spec.Ed25519.basePoint (16 * 16) := by
    rw [vb, constPoint_eval, after_top _ _ _ hscalar]
  have bbits : ∀ i < 16 * 16, b.mem (off base (768 + i)) = BitVec.ofNat 8 ((scalar / 2 ^ i) % 2) := by
    intro i hi
    rw [kb.bit _ (by omega), abits i hi]
  have btab : ∀ i < 16, tablePoint b.mem base (1280 + 128 * i) =
      powerPoint Spec.Ed25519.basePoint (16 * i) := by
    intro i hi
    rw [workspace_tablePoint kb.mem (by omega) (by omega)]
    exact (atab i hi).trans (baseCheckpoint_ok i hi)
  have kab := kat.trans (PowersKeep.of_keep kb)
  refine WP.mono (mulCounterInit_ok (kab.scratch hs) 16) fun c ⟨cc, cg, cr, cw, cm⟩ => ?_
  have kc : PowersKeep base 56 7368 b c := ⟨fun r _ _ hr => cg r (by
    intro he; subst r; exact hr (by decide)), cr, cw, (TableFrame.table cm).mono (by decide) (by decide)⟩
  have ce := header_env cm
  exact ⟨by decide, Nat.le_refl _, (kab.trans kc).scratch hs, cc,
    (by rw [ce]; exact bd), (by rw [ce]; exact bp),
    (by intro i hi; rw [cm _ (by rw [Proof.X25519.X86_64.ofs_off' base (by omega)]; omega)]; exact bbits i hi),
    (by intro i hi; rw [(TableFrame.table cm).point (by omega) (Or.inr (by omega)) (by omega)]; exact btab i hi),
    kab.trans kc⟩

theorem baseMultiplyPrecomputed_ok {s : State} {base : Addr} (hs : Scratch s base)
    (scalar : Nat) (hscalar : scalar < 2 ^ (16 * 16))
    (hd : env s.mem base 16 = Spec.Ed25519.d)
    (hb : ∀ i < 16 * 16, s.mem (off base (768 + i)) = BitVec.ofNat 8 ((scalar / 2 ^ i) % 2)) :
    WP isa baseMultiplyPrecomputed s fun t =>
      point (env t.mem base) 0 1 2 3 = Spec.Ed25519.pointMul scalar Spec.Ed25519.basePoint ∧
      env t.mem base 16 = Spec.Ed25519.d ∧ PowersKeep base 56 7368 s t := by
  rw [baseMultiplyPrecomputed]
  refine WP.seq (WP.mono (baseMultiplyPrecomputedInit_ok hs scalar hscalar hd hb) fun a h => ?_)
  refine WP.mono (pointMulLoop_ok h.scratch 16 scalar _ (by decide) (by decide)
    h.counter h.d h.value h.bits h.table) fun t ⟨tv, td, kt⟩ => ?_
  exact ⟨tv, td, h.keep.trans kt⟩

end VG.Proof.Ed25519.X86_64
