import VerifiedGarbage.Proof.X25519.AArch64.Word.Input
import VerifiedGarbage.Proof.Ed25519.AArch64.ScalarMemory
import VerifiedGarbage.Proof.Ed25519.AArch64.Codec

/-! Canonical field encoding and restoration of the caller's registers. -/
namespace VG.Proof.X25519.AArch64.Word
open VG VG.AArch64 VG.Spec.X25519 VG.Proof.X25519
open VG.Impl.Ed25519.AArch64 VG.Proof.Ed25519.AArch64
open VG.Proof.Ed25519.Word64

theorem restore_ok {s : State} {base : Addr} (hb : s.gpr .x0 = base)
    (hw : (⟨base, 4096⟩ : Region) ∈ s.wr) {g : Reg → BitVec 64} (hsv : Saved base g s.mem) :
    WP isa (.block (saved.map (fun (r,o) => VG.Impl.Ed25519.AArch64.ld r o))) s fun t =>
      (∀ rd ∈ saved, t.gpr rd.1 = g rd.1) ∧ Keeps [.x19, .x20, .x21, .x22, .x23, .x24] s t := by
  have hr : ∀ d, d + 8 ≤ 4096 → InRegions (s.rd ++ s.wr) (off base d) 8 :=
    fun d hd => ⟨_, List.mem_append_right _ hw, contains_scWith (large := false) hd⟩
  apply WP.of_runBlock
  simp only [VG.Impl.Ed25519.AArch64.ld, saved, List.map_cons, List.map_nil, runBlock_cons, runStep_some, runBlock_nil,
    exec, addr, Size.bytes, State.load, RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write,
    RegUpd.wr_write, hb, BitVec.setWidth_eq, Nat.reduceMod, Nat.reduceMul, Nat.reduceLT, and_self,
    hr 0 (by omega), hr 8 (by omega), hr 16 (by omega), hr 24 (by omega), hr 32 (by omega), hr 40 (by omega),
    ite_true, ite_false, reduceCtorEq, Option.bind_some, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨fun rd hrd => ?_, ⟨?_, rfl, rfl, rfl, rfl⟩⟩
  · have e := hsv rd hrd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hrd
    rcases hrd with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simpa only [RegUpd.gpr_write, ite_true, ite_false, reduceCtorEq, word, Mem.readW,
        BitVec.setWidth_eq] using e
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1,
      hr.2.2.2.2.1, hr.2.2.2.2.2, ite_false]

theorem out_ok {s : State} {q : Addr} (hq : s.gpr .x1 = q) (hw : (⟨q, 32⟩ : Region) ∈ s.wr) :
    WP isa (.block [.str .x .x4 .x1 0, .str .x .x5 .x1 8, .str .x .x6 .x1 16, .str .x .x7 .x1 24]) s
      fun t => t = { s with mem := st4 s.mem q 0 (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7) } := by
  have w : ∀ d, d + 8 ≤ 32 → InRegions s.wr (off q d) 8 :=
    fun d hd => ⟨_, hw, Offset.contains_base q hd (by omega)⟩
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, addr, Size.bytes, State.store, read_x,
    hq, BitVec.setWidth_eq, Nat.reduceMod, Nat.reduceMul, Nat.reduceLT, and_self, ite_true,
    w 0 (by omega), w 8 (by omega), w 16 (by omega), w 24 (by omega),
    Option.bind_some, Option.some.injEq, exists_eq_left']
  rfl



theorem saved_output {base q : Addr} {m : Mem} {g : Reg → BitVec 64}
    (hs : Saved base g m) (hd : (⟨q,32⟩ : Region).Disjoint ⟨base,4096⟩)
    (w0 w1 w2 w3 : BitVec 64) : Saved base g (st4 m q 0 w0 w1 w2 w3) := by
  have hf : Frame [⟨q,32⟩] m (st4 m q 0 w0 w1 w2 w3) := by
    exact ((((Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains_base q (d := 0) (by decide) (by decide))).writeW (List.mem_singleton_self _) _
      (Offset.contains_base q (d := 8) (by decide) (by decide))).writeW (List.mem_singleton_self _) _
      (Offset.contains_base q (d := 16) (by decide) (by decide))).writeW (List.mem_singleton_self _) _
      (Offset.contains_base q (d := 24) (by decide) (by decide))
  intro rd hr
  have hh : rd.2+8 ≤ 4096 := by
    simp only [saved,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  change (st4 m q 0 w0 w1 w2 w3).readW (off base rd.2) 64 = g rd.1
  rw [hf.readW (a := off base rd.2) (w := 64) (r := ⟨base,4096⟩) (Offset.contains_base base hh (by omega))
    (by simp only [List.mem_singleton,forall_eq]; exact hd.symm) (by decide)]
  exact hs rd hr

theorem keeps_kp {s t : State} {rs : List Reg} (h : Keeps rs s t)
    (hr : rs ⊆ clob ++ ([.x1,.x19] : List Reg)) : Kp (clob ++ ([.x1,.x19] : List Reg)) s t :=
  ⟨fun r hn => h.gpr r (fun hh => hn (hr hh)),h.rd,h.wr⟩

theorem field_kp {base : Addr} {s t : State} (h : Keep base s t) : Kp (clob ++ ([.x1,.x19] : List Reg)) s t :=
  ⟨fun r hr => h.gpr r (fun hh => hr (List.mem_append_left _ hh)),h.rd,h.wr⟩


theorem serialize_ok {base q : Addr} {s : State} {g : Reg → BitVec 64}
    (hs : Scratch s base) (ho : s.gpr .x1 = q)
    (hw : (⟨q,32⟩ : Region) ∈ s.wr) (hd : (⟨q,32⟩ : Region).Disjoint ⟨base,4096⟩)
    (hsv : Saved base g s.mem) :
    WP isa (.block (([.str .x .x4 .x1 0,.str .x .x5 .x1 8,.str .x .x6 .x1 16,.str .x .x7 .x1 24] : List Instr) ++
      saved.map (fun (r,o) => VG.Impl.Ed25519.AArch64.ld r o))) s fun t =>
      (∀ rd ∈ saved, t.gpr rd.1 = g rd.1) ∧ Kp (clob ++ ([.x1,.x19] : List Reg)) s t ∧
      bytesAt t.mem q 32 = leBytes 32 (val4 (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7)) := by
  rw [WP.block_append_iff]
  refine WP.mono (out_ok ho hw) fun d de => ?_
  subst d
  have svd := saved_output hsv hd (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7)
  refine WP.mono (restore_ok (s := {s with mem := st4 s.mem q 0 (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7)})
    (g := g) hs.x0 hs.wr svd) fun t ⟨tg,kt⟩ => ?_
  have ko : Kp (clob ++ ([.x1,.x19] : List Reg)) s
      {s with mem := st4 s.mem q 0 (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7)} :=
    ⟨fun _ _ => rfl,rfl,rfl⟩
  exact ⟨tg,ko.trans (keeps_kp kt (by decide)) |>.sub (by decide),by rw [kt.mem,bytesAt_st4]⟩

theorem finish_ok {base q : Addr} {s : State} {g : Reg → BitVec 64}
    (hs : Scratch s base) (ho : s.gpr .x1 = q)
    (hw : (⟨q,32⟩ : Region) ∈ s.wr) (hd : (⟨q,32⟩ : Region).Disjoint ⟨base,4096⟩)
    (hsv : Saved base g s.mem) :
    WP isa (.block VG.Impl.X25519.AArch64.Word.finish) s fun t =>
      (∀ rd ∈ saved, t.gpr rd.1 = g rd.1) ∧
      Kp (clob ++ ([.x1,.x19] : List Reg)) s t ∧
      bytesAt t.mem q 32 = encodeUCoordinate (env s.mem base 1 * env s.mem base 15) := by
  rw [VG.Impl.X25519.AArch64.Word.finish]
  simp only [VG.Impl.X25519.AArch64.Word.freeze,List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.AArch64.mul_ok hs (slot_rangeWith (large := false) 1)
    (slot_rangeWith (large := false) 1) (slot_rangeWith (large := false) 15)) fun a ⟨ka,ea⟩ => ?_
  have kma := op_keep (o := 1) ka
  have sva := hsv.outside kma.mem (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.AArch64.freeze_ok (kma.scr hs) (slot_rangeWith (large := false) 1)) fun b ⟨bv,kb⟩ => ?_
  have hb := (kma.scr hs).of_keeps kb (by decide)
  refine WP.mono (serialize_ok (g := g) hb
    (by rw [kb.gpr _ (by decide),kma.gpr _ (by decide),ho])
    (by rw [kb.wr,kma.wr]; exact hw) hd (by rw [kb.mem]; exact sva)) fun t ⟨tg,kt,rt⟩ => ?_
  refine ⟨tg,?_,?_⟩
  · exact ((field_kp kma).trans (keeps_kp kb (by decide))).trans kt |>.sub (by decide)
  · rw [rt,encodeUCoordinate_eq,bv]
    exact congrArg (leBytes 32) (congrArg Fin.val ea)

end VG.Proof.X25519.AArch64.Word
