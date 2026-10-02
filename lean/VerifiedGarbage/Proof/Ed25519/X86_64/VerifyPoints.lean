import VerifiedGarbage.Proof.Ed25519.X86_64.WindowLoop
import VerifiedGarbage.Proof.Ed25519.X86_64.PointEqual
import VerifiedGarbage.Proof.Ed25519.X86_64.PointMul
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-!
# Verification's equation, from the windows

Untrusted. The windows leave a representative of `[k]A - [S]B`, compared
with `-R`: they are equal exactly when `[S]B = R + [k]A`, which, as `A` and
`R` represent points of the group, is the specification's comparison.
-/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64 VG.Proof.Ed25519 Edwards
open VG.Proof.X25519.X86_64 (off ofs Keeps clob Outside)

variable {fld : Arith} [EdArith fld]

theorem PowersKeep.of_byte {base : Addr} {s t : State} (h : ByteKeep base s t) :
    PowersKeep base 56 7752 s t :=
  ⟨fun r hb hs hc => h.gpr r hc hb hs, h.rd, h.wr, TableFrame.table (h.mem.mono (by decide) (by decide))⟩

theorem negR_eval (e : Env) :
    point (evalOps [.const 8 0, .sub 4 8 4, .sub 7 8 7] e) 0 1 2 3 = point e 0 1 2 3 ∧
    point (evalOps [.const 8 0, .sub 4 8 4, .sub 7 8 7] e) 4 5 6 7 = negPoint (point e 4 5 6 7) :=
  ⟨rfl, rfl⟩

/-- `-R`, beside the accumulator. -/
theorem negR_ok {s : State} {base : Addr} (hs : Scratch s base) :
    WP isa (.block (negR fld)) s fun t => Keep base s t ∧
      point (env t.mem base) 0 1 2 3 = point (env s.mem base) 0 1 2 3 ∧
      point (env t.mem base) 4 5 6 7 = negPoint (tablePoint s.mem base 7552) := by
  rw [negR, List.append_assoc, WP.block_append_iff]
  refine WP.mono (tableStart_ok hs.rdi 7552) fun a ⟨ap, ka⟩ => ?_
  have kae : Keep base s a := Keep.of_keeps ka (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (pointFromTableQ_ok (hs.of_keep kae) ap (by decide) (by decide)) fun b ⟨pb, kb⟩ => ?_
  have kbe := Keep.of_tableQ kb
  have b_low : ∀ i : Slot, i.val < 4 → env b.mem base i = env s.mem base i := by
    intro i hi
    change Proof.X25519.X86_64.F b.mem base (offset i) = Proof.X25519.X86_64.F s.mem base (offset i)
    rw [Outside_F kb.mem (by simp only [offset]; omega) (Or.inl (by simp only [offset]; omega)), ka.2.1]
  refine WP.mono (fieldCodeWide_ok ((hs.of_keep kae).of_keep kbe) _) fun t ⟨kt, vt⟩ => ?_
  refine ⟨(kae.trans kbe).trans kt, ?_, ?_⟩
  · rw [vt, (negR_eval _).1]
    simp only [point, b_low 0 (by decide), b_low 1 (by decide), b_low 2 (by decide),
      b_low 3 (by decide)]
  · rw [vt, (negR_eval _).2, pb, ka.2.1]

/-- Verification's code before the windows, regrouped. -/
def windowPrep (fld : Arith) : Prog isa :=
  .seq (.seq (.seq (.block windowSetup) (aTable fld)) (.block bTable)) (.block (windowInit fld))

/-- Before the windows: the tables, an accumulator representing `0` and the counter at 64. -/
theorem windowPrep_ok {s : State} {base sig challenge : Addr} {Aa : EPoint dZ}
    (hs : Scratch s base)
    (hp : s.mem.readW (off base 7944) 64 = sig)
    (hc : s.mem.readW (off base 7952) 64 = challenge)
    (hr : ∀ i < 32, InRegions (s.rd ++ s.wr) (off (off sig 32) i) 1)
    (hf : ∀ i < 32, 8192 ≤ ofs base (off (off sig 32) i))
    (hcr : ∀ i < 64, InRegions (s.rd ++ s.wr) (off challenge i) 1)
    (hcf : ∀ i < 64, 8192 ≤ ofs base (off challenge i))
    (hA : Rep (tablePoint s.mem base 7424) Aa) :
    WP isa (windowPrep fld) s fun e => WinLoop e base challenge sig Aa
      (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem challenge 64))
      (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (off sig 32) 32)) 64 e ∧
      PowersKeep base 56 7752 s e ∧ tablePoint e.mem base 7552 = tablePoint s.mem base 7552 := by
  rw [windowPrep]
  -- The constant `d`.
  refine WP.seq (WP.seq (WP.seq (WP.mono (constFieldWide_ok hs 16 Spec.Ed25519.d) fun a ⟨ka, va⟩ => ?_)))
  have ad : env a.mem base 16 = Spec.Ed25519.d := by rw [va]; exact Function.update_self ..
  have aA : tablePoint a.mem base 7424 = tablePoint s.mem base 7424 :=
    workspace_tablePoint ka.mem (by decide) (by decide)
  have aR : tablePoint a.mem base 7552 = tablePoint s.mem base 7552 :=
    workspace_tablePoint ka.mem (by decide) (by decide)
  have ksa : PowersKeep base 56 7752 s a := PowersKeep.of_keep ka
  -- The multiples of `A`.
  refine WP.mono (aTable_ok (ksa.scratch hs) ad (by rw [aA]; exact hA)) fun b hb => ?_
  have ksb := ksa.trans (hb.keep.mono (by decide) (by decide))
  have bR : tablePoint b.mem base 7552 = tablePoint s.mem base 7552 := by
    rw [hb.keep.mem.point (by decide) (Or.inr (by decide)) (by decide), aR]
  -- The negated multiples of `B`.
  refine WP.mono (bTable_ok hb.scratch) fun c hc' => ?_
  have kbc : PowersKeep base 56 7752 b c :=
    ⟨fun r _ _ hr => hc'.gpr r (fun hm => hr (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl | rfl | rfl | rfl <;> decide)), hc'.rd, hc'.wr,
      TableFrame.table (hc'.mem.mono (by decide) (by decide))⟩
  have ksc := ksb.trans kbc
  have cR : tablePoint c.mem base 7552 = tablePoint s.mem base 7552 := by
    rw [(TableFrame.table hc'.mem).point (by decide) (Or.inr (by decide)) (by decide), bR]
  have cd : env c.mem base 16 = Spec.Ed25519.d := by rw [table_env hc'.mem (by decide)]; exact hb.d
  have cA : TableOf id c.mem base 5376 Aa := fun j hj =>
    ⟨_, ((TableFrame.table hc'.mem).point (by omega) (Or.inr (by omega)) (by omega)), hb.table j hj⟩
  have cB : TableOf cache c.mem base 2048 (-baseAff) := fun j hj => by
    obtain ⟨q, hq, hr⟩ := negBaseCached_ok j hj
    exact ⟨q, by rw [hc'.table j hj, hq], hr⟩
  -- The accumulator and the byte counter.
  rw [windowInit, WP.block_append_iff]
  refine WP.mono (fieldCodeWide_ok (ksc.scratch hs) (constPointOps Spec.Ed25519.identity))
    fun d ⟨kd, vd⟩ => ?_
  have kcd : PowersKeep base 56 7752 c d := PowersKeep.of_keep kd
  refine WP.mono (mulCounterInit_ok ((ksc.trans kcd).scratch hs) 64) fun e ⟨ec, eg, er, ew, em⟩ => ?_
  have kde : ByteKeep base d e :=
    ⟨fun r _ _ _ => eg r (by rintro rfl; contradiction), er, ew, em.mono (by decide) (by decide)⟩
  have kce : ByteKeep base c e := (ByteKeep.of_win (WinKeep.of_keep kd)).trans kde
  have kse := ksc.trans (PowersKeep.of_byte kce)
  have eR : tablePoint e.mem base 7552 = tablePoint s.mem base 7552 := by
    rw [win_tablePoint kce.mem (by decide) (by decide), cR]
  have ed : env e.mem base 16 = Spec.Ed25519.d := by rw [header_env em, vd]; exact cd
  have ctx : WinCtx base challenge sig Aa e :=
    ⟨kse.scratch hs, (kse.header (by decide) (by decide) (by decide)).trans hc,
      (kse.header (by decide) (by decide) (by decide)).trans hp,
      fun i hi => by rw [kse.rd, kse.wr]; exact hcr i hi,
      fun i hi => by rw [kse.rd, kse.wr]; exact hr i hi, hcf, hf,
      cA.of_win kce.mem (by decide) (by decide), cB.of_win kce.mem (by decide) (by decide)⟩
  have hK : Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt e.mem challenge 64) < 256 ^ 64 := by
    have h := decodeLE_lt (Spec.Ed25519.bytesAt e.mem challenge 64)
    rwa [show (Spec.Ed25519.bytesAt e.mem challenge 64).length = 64 by
      simp [Spec.Ed25519.bytesAt]] at h
  have hS := decodeLE_lt32 e.mem (off sig 32)
  have eK := outside_bytes (tableFrame_work kse.mem (by decide) (by decide)) (by decide) hcf
  have eS := outside_bytes (tableFrame_work kse.mem (by decide) (by decide)) (by decide) hf
  refine ⟨⟨ctx, ed, ec, by rw [eK], by rw [eS], ?_, ⟨fun _ _ _ _ => rfl, rfl, rfl, Outside.refl _ _ _ _⟩⟩,
    kse, eR⟩
  rw [← eK, ← eS, Nat.div_eq_of_lt hK, Nat.div_eq_of_lt (Nat.lt_trans hS (by decide)), zero_smul,
    zero_smul, add_zero, header_env em, vd, constPoint_eval]
  exact identity_rep

theorem verifyEquationPoints_ok {s : State} {base sig challenge : Addr} {Aa Ra : EPoint dZ}
    (hs : Scratch s base)
    (hp : s.mem.readW (off base 7944) 64 = sig)
    (hc : s.mem.readW (off base 7952) 64 = challenge)
    (hr : ∀ i < 32, InRegions (s.rd ++ s.wr) (off (off sig 32) i) 1)
    (hf : ∀ i < 32, 8192 ≤ ofs base (off (off sig 32) i))
    (hcr : ∀ i < 64, InRegions (s.rd ++ s.wr) (off challenge i) 1)
    (hcf : ∀ i < 64, 8192 ≤ ofs base (off challenge i))
    (hA : Rep (tablePoint s.mem base 7424) Aa) (hR : Rep (tablePoint s.mem base 7552) Ra) :
    WP isa (verifyEquationPoints fld) s fun t => PowersKeep base 56 7752 s t ∧
      t.gpr .rax = signWord (Spec.Ed25519.pointEqual
        (Spec.Ed25519.pointMul
          (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (off sig 32) 32)) Spec.Ed25519.basePoint)
        (Spec.Ed25519.pointAdd (tablePoint s.mem base 7552)
          (Spec.Ed25519.pointMul (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem challenge 64))
            (tablePoint s.mem base 7424)))) := by
  rw [verifyEquationPoints]
  apply WP.assoc; apply WP.assoc; apply WP.assoc
  refine WP.seq (WP.mono (windowPrep_ok hs hp hc hr hf hcr hcf hA) fun e ⟨w0, kse, eR⟩ => ?_)
  -- The windows.
  refine WP.seq (WP.mono (loopA_ok w0) fun f hf' => ?_)
  refine WP.seq (WP.mono (loopB_ok hf') fun g hg => ?_)
  have ksg := kse.trans (PowersKeep.of_byte hg.keep)
  -- The comparison with `-R`.
  refine WP.seq (WP.mono (negR_ok (ksg.scratch hs)) fun u ⟨ku, u0, u4⟩ => ?_)
  have ksu := ksg.trans (PowersKeep.of_keep ku)
  refine WP.mono (pointEqual_ok (ksu.scratch hs)) fun t ⟨kt, tv⟩ => ?_
  refine ⟨ksu.trans (PowersKeep.of_keep kt), ?_⟩
  have gv := hg.value
  simp only [pow_zero, Nat.div_one] at gv
  rw [tv, u0, u4, win_tablePoint hg.keep.mem (by decide) (by decide), eR,
    window_equation hA hR gv.proj hR.neg.proj]

end VG.Proof.Ed25519.X86_64
