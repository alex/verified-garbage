import VerifiedGarbage.Proof.Ed25519.AArch64.WindowLoop
import VerifiedGarbage.Proof.Ed25519.AArch64.WindowTables
import VerifiedGarbage.Proof.Ed25519.AArch64.PointEqual
import VerifiedGarbage.Proof.Ed25519.AArch64.PointMul
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-!
# Verification's equation, from the windows

Untrusted. The windows leave a representative of `[k]A - [S]B`, compared
with `-R`: they are equal exactly when `[S]B = R + [k]A`, which, as `A` and
`R` represent points of the group, is the specification's comparison.
-/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64 VG.Proof.Ed25519 Edwards

theorem PowersKeep.of_byte {base : Addr} {s t : State} (h : ByteKeep base s t) :
    PowersKeep base 56 7752 s t :=
  ⟨fun r hb hs hc => h.gpr r hc hb hs, h.rd, h.wr, h.sp,
    TableFrame.table (h.mem.mono (by decide) (by decide))⟩

theorem negR_eval (e : Env) :
    point (evalOps [.const 8 0, .sub 4 8 4, .sub 7 8 7] e) 0 1 2 3 = point e 0 1 2 3 ∧
    point (evalOps [.const 8 0, .sub 4 8 4, .sub 7 8 7] e) 4 5 6 7 = negPoint (point e 4 5 6 7) :=
  ⟨rfl, rfl⟩

/-- `-R`, beside the accumulator. -/
theorem negR_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (.block negR) s fun t => CounterKeep base s t ∧
      point (env t.mem base) 0 1 2 3 = point (env s.mem base) 0 1 2 3 ∧
      point (env t.mem base) 4 5 6 7 = negPoint (tablePoint s.mem base 7552) := by
  rw [negR, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (tableIndexZero_ok s) fun a ⟨az, ka⟩ => ?_
  have kar : CounterKeep base s a := CounterKeep.of_keeps ka (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (tableAddr_ok (kar.scr hs).x0 7552 0 (by decide) az) fun b ⟨pb, kb⟩ => ?_
  simp only [Nat.mul_zero, Nat.add_zero] at pb
  have kbe : Keep base a b := Keep.of_keeps kb (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (pointFromTableQ_ok (kbe.scr (kar.scr hs)) pb (by decide) (by decide))
    fun c ⟨pc, kc⟩ => ?_
  have kce := Keep.of_tableQ kc
  have o := tableQ_other kc
  have c0 : point (env c.mem base) 0 1 2 3 = point (env s.mem base) 0 1 2 3 := by
    simp only [point, o 0 (by decide), o 1 (by decide), o 2 (by decide), o 3 (by decide), kb.mem,
      ka.mem]
  refine WP.mono (fieldCode_ok _ (kce.scr (kbe.scr (kar.scr hs)))) fun t ⟨kt, vt⟩ => ?_
  refine ⟨kar.trans (CounterKeep.of_keep ((kbe.trans kce).trans kt)), ?_, ?_⟩
  · rw [vt, (negR_eval _).1, c0]
  · rw [vt, (negR_eval _).2, pc, kb.mem, ka.mem]

/-- Verification's code before the windows, regrouped. -/
def windowPrep : Prog isa :=
  .seq (.seq (.seq (.block windowSetup) aTable) (.block bTable)) (.block windowInit)

theorem PowersKeep.of_table {base : Addr} {s t : State} {o n : Nat} (h : TableKeep base o n s t)
    (ho : 56 ≤ o) (hn : o + n ≤ 7808) : PowersKeep base 56 7752 s t :=
  ⟨fun r _ _ hr => h.gpr r (fun hm => hr (by
    revert hm; simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro (rfl | rfl | rfl | rfl) <;> decide)), h.rd, h.wr, h.sp,
    TableFrame.table (h.mem.mono (by omega) (by omega))⟩

/-- Before the windows: the tables, an accumulator representing `0` and the counter at 64. -/
theorem windowPrep_ok {s : State} {base sig challenge : Addr} {Aa : EPoint dZ}
    (hs : Scr s base)
    (hp : s.mem.readW (off base 7944) 64 = sig)
    (hc : s.mem.readW (off base 7952) 64 = challenge)
    (hr : ∀ i < 32, InRegions (s.rd ++ s.wr) (off (off sig 32) i) 1)
    (hf : ∀ i < 32, 8192 ≤ ofs base (off (off sig 32) i))
    (hcr : ∀ i < 64, InRegions (s.rd ++ s.wr) (off challenge i) 1)
    (hcf : ∀ i < 64, 8192 ≤ ofs base (off challenge i))
    (hA : Rep (tablePoint s.mem base 7424) Aa) :
    WP isa windowPrep s fun e => WinLoop e base challenge sig Aa
      (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem challenge 64))
      (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (off sig 32) 32)) 64 e ∧
      PowersKeep base 56 7752 s e ∧ tablePoint e.mem base 7552 = tablePoint s.mem base 7552 := by
  rw [windowPrep]
  -- The constant `d`.
  refine WP.seq (WP.seq (WP.seq (WP.mono (constField_ok hs 16 Spec.Ed25519.d) fun a ⟨ka, va⟩ => ?_)))
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
  refine WP.mono (bTable_ok hb.scratch) fun c ⟨ct, kc⟩ => ?_
  have ksc := ksb.trans (PowersKeep.of_table kc (by decide) (by decide))
  have cR : tablePoint c.mem base 7552 = tablePoint s.mem base 7552 := by
    rw [(TableFrame.table kc.mem).point (by decide) (Or.inr (by decide)) (by decide), bR]
  have cd : env c.mem base 16 = Spec.Ed25519.d := by rw [table_env kc.mem (by decide)]; exact hb.d
  have cA : TableOf cache c.mem base 5376 Aa := fun j hj => by
    obtain ⟨q, hq, hr⟩ := hb.table j hj
    exact ⟨q, by rw [(TableFrame.table kc.mem).point (by omega) (Or.inr (by omega)) (by omega)]; exact hq,
      hr⟩
  have cB : TableOf cache c.mem base 2048 (-baseAff) := fun j hj => by
    obtain ⟨q, hq, hr⟩ := negBaseCached_ok j hj
    exact ⟨q, by rw [ct j hj, hq], hr⟩
  -- The accumulator and the byte counter.
  rw [windowInit, WP.block_append_iff]
  refine WP.mono (fieldCode_ok (constPointOps Spec.Ed25519.identity) (ksc.scratch hs))
    fun d ⟨kd, vd⟩ => ?_
  have kcd : PowersKeep base 56 7752 c d := PowersKeep.of_keep kd
  refine WP.mono (mulCounterInit_ok ((ksc.trans kcd).scratch hs) 64)
    fun e ⟨ec, eg, er, ew, esp, em⟩ => ?_
  have kde : ByteKeep base d e :=
    ⟨fun r _ _ _ => eg r (by rintro rfl; contradiction), er, ew, esp, em.mono (by decide) (by decide)⟩
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
  have hK := decodeLE_lt64 e.mem challenge
  have hS := decodeLE_lt32 e.mem (off sig 32)
  have eK := outside_bytes (tableFrame_work kse.mem (by decide) (by decide)) (by decide) hcf
  have eS := outside_bytes (tableFrame_work kse.mem (by decide) (by decide)) (by decide) hf
  refine ⟨⟨ctx, ed, ec, by rw [eK], by rw [eS], ?_, ByteKeep.refl _ _⟩, kse, eR⟩
  rw [← eK, ← eS, Nat.div_eq_of_lt hK, Nat.div_eq_of_lt (Nat.lt_trans hS (by decide)), zero_smul,
    zero_smul, add_zero, header_env em, vd, constPoint_eval]
  exact identity_rep.proj

theorem verifyEquationPoints_ok {s : State} {base sig challenge : Addr} {Aa Ra : EPoint dZ}
    (hs : Scr s base)
    (hp : s.mem.readW (off base 7944) 64 = sig)
    (hc : s.mem.readW (off base 7952) 64 = challenge)
    (hr : ∀ i < 32, InRegions (s.rd ++ s.wr) (off (off sig 32) i) 1)
    (hf : ∀ i < 32, 8192 ≤ ofs base (off (off sig 32) i))
    (hcr : ∀ i < 64, InRegions (s.rd ++ s.wr) (off challenge i) 1)
    (hcf : ∀ i < 64, 8192 ≤ ofs base (off challenge i))
    (hA : Rep (tablePoint s.mem base 7424) Aa) (hR : Rep (tablePoint s.mem base 7552) Ra) :
    WP isa verifyEquationPoints s fun t => PowersKeep base 56 7752 s t ∧
      t.gpr .x8 = signWord (Spec.Ed25519.pointEqual
        (Spec.Ed25519.pointMul
          (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (off sig 32) 32)) Spec.Ed25519.basePoint)
        (Spec.Ed25519.pointAdd (tablePoint s.mem base 7552)
          (Spec.Ed25519.pointMul (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem challenge 64))
            (tablePoint s.mem base 7424)))) := by
  rw [verifyEquationPoints]
  apply WP.assoc; apply WP.assoc; apply WP.assoc
  refine WP.seq (WP.mono (windowPrep_ok hs hp hc hr hf hcr hcf hA) fun e ⟨w0, kse, eR⟩ => ?_)
  -- The windows.
  refine WP.seq (WP.mono (skipZero_ok w0) fun f ⟨c, hc32, hc64, hf'⟩ => ?_)
  refine WP.seq (WP.mono (windowsA_ok hc32 hc64 hf') fun g hg => ?_)
  refine WP.seq (WP.mono (loopB_ok hg) fun h hh => ?_)
  have ksh := kse.trans (PowersKeep.of_byte hh.keep)
  -- The comparison with `-R`.
  refine WP.seq (WP.mono (negR_ok (ksh.scratch hs)) fun u ⟨ku, u0, u4⟩ => ?_)
  have ksu := ksh.trans (PowersKeep.of_counter ku)
  refine WP.mono (pointEqual_ok (ksu.scratch hs)) fun t ⟨kt, tv⟩ => ?_
  refine ⟨ksu.trans (PowersKeep.of_keep kt), ?_⟩
  have hv := hh.value
  simp only [pow_zero, Nat.div_one] at hv
  rw [tv, u0, u4, win_tablePoint hh.keep.mem (by decide) (by decide), eR,
    window_equation hA hR hv hR.neg.proj]

end VG.Proof.Ed25519.AArch64
