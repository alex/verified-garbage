import VerifiedGarbage.Proof.X25519.AArch64.Word.Ladder
import VerifiedGarbage.Proof.X25519.AArch64.Top
import VerifiedGarbage.Proof.Ed25519.AArch64.DecodeBits
import VerifiedGarbage.Proof.Ed25519.Bytes

/-! Decode RFC 7748 inputs into four-word fields. -/
namespace VG.Proof.X25519.AArch64.Word
open VG VG.AArch64 VG.Spec.X25519 VG.Proof.X25519
open VG.Impl.Ed25519.AArch64 VG.Proof.Ed25519.AArch64
open VG.Proof.Ed25519.Word64

abbrev Kp := VG.Proof.X25519.AArch64.Kp
abbrev Sc := VG.Proof.X25519.AArch64.Sc

theorem outside_frame {base : Addr} {m m' : Mem} {d n : Nat}
    (h : Outside base d n m m') (hn : d+n ≤ 4096) : Frame [⟨base,4096⟩] m m' := by
  intro x hx
  apply h x
  have hh := hx _ (List.mem_singleton_self _)
  simp only [Region.Contains] at hh
  right
  change d+n ≤ (x-base).toNat
  omega

theorem base_ok {base : Addr} {s : State} (hs : Sc base s)
    (hn : base.toNat + 4096 ≤ 2^64) :
    WP isa (.block [VG.Impl.X25519.AArch64.st .x0 48, mov .x1 .x0, mov .x0 .x3]) s fun t =>
      Scratch t base ∧ t.gpr .x1 = s.gpr .x0 ∧ word t.mem base 48 = s.gpr .x0 ∧
      Kp [.x0,.x1] s t ∧ Outside base 48 8 s.mem t.mem := by
  rw [WP.block_cons_iff]
  refine ⟨_, VG.Proof.X25519.AArch64.exec_st hs .x0 (off := 48) (by decide), ?_⟩
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, mov,
    exec_addImm_x (by decide : 0 < 4096), read_x, BitVec.add_zero, RegUpd.gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq, Option.some.injEq, exists_eq_left']
  exact ⟨⟨hs.x3,hs.wr,hn⟩, trivial, Mem.readW_writeW_self64 _ _ _,
    ⟨fun r hr => by simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr; simp only [RegUpd.gpr_write,hr.1,hr.2,ite_false],rfl,rfl⟩,
    writeW_outside _ _ _ (by decide)⟩

theorem initGood (e : Env) (x : Fe) (hx : e 0 = x) :
    Good (evalOps ([.copy 3 0, .const 1 1, .const 2 0, .const 4 1, .const 18 121665] : List FieldOp) e) x (init x) :=
  ⟨hx, rfl, rfl, hx, rfl, rfl⟩


theorem decode_ok {base p : Addr} {s : State} (hs : Scratch s base)
    (hp : s.gpr .x2 = p)
    (hr : ∀ d, d+8 ≤ 32 → InRegions (s.rd ++ s.wr) (off p d) 8) :
    WP isa (.block (loadY ++ store4 (offset 0))) s fun t =>
      Keep base s t ∧ env t.mem base 0 = toFe (decodeUCoordinate (bytesAt s.mem p 32)) := by
  rw [WP.block_append_iff]
  refine WP.mono (loadY_ok s p hp hr) fun a ⟨av,ka⟩ => ?_
  refine WP.mono (store4_ok (hs.of_keeps ka (by decide)) (slot_rangeWith (large := false) 0)) fun t ht => ?_
  subst t
  refine ⟨⟨fun r hr => ka.gpr r (fun hh => hr (by simp only [clob, List.mem_cons, List.not_mem_nil, or_false] at *; tauto)),
    ka.rd,ka.wr,ka.sp,?_,⟩,?_,⟩
  · rw [ka.mem]
    exact (st4_outside _ _ (by decide : offset 0+32<2^64) _ _ _ _).mono (by decide) (by decide)
  · change toFe (fe _ _ _) = _
    rw [fe_st4 _ _ (by decide), av, VG.Proof.Ed25519.decodeLE_eq,
      decodeUCoordinate_eq (length_bytesAt _ _ _)]
    rfl

theorem init_ok {base : Addr} {s : State} {x : Fe} (hs : Scratch s base)
    (hx : env s.mem base 0 = x) :
    WP isa (.block (fieldCode ([.copy 3 0, .const 1 1, .const 2 0, .const 4 1, .const 18 121665] : List FieldOp) ++
      ([.movz .x .x2 0 0, VG.Impl.Ed25519.AArch64.st .x2 768] : List Instr))) s fun t =>
      LoopKeep base s t ∧ Good (env t.mem base) x (init x) ∧ word t.mem base 768 = 0 := by
  rw [WP.block_append_iff]
  refine WP.mono (fieldCode_ok _ hs) fun a ⟨ka,ea⟩ => ?_
  have ga := initGood (env s.mem base) x hx
  rw [← ea] at ga
  rw [WP.block_cons_iff]
  refine ⟨_, VG.Proof.X25519.AArch64.exec_movz, ?_⟩
  have kb : Keeps [.x2] a (a.write .x .x2 0) :=
    ⟨fun r hr => RegUpd.gpr_write_of_ne _ _ _ (by simpa only [List.mem_singleton] using hr),rfl,rfl,rfl,rfl⟩
  have kab := (LoopKeep.of_field ka).trans (LoopKeep.of_keeps kb (by decide))
  refine WP.mono (storeSwap_ok (kab.scratch hs)) fun t ⟨kt,et,wt,_⟩ => ?_
  exact ⟨kab.trans kt, by rw [et,RegUpd.mem_write]; exact ga,
    wt.trans (RegUpd.gpr_write_self _ _ _ _)⟩


theorem LoopKeep.kp {base : Addr} {s t : State} (h : LoopKeep base s t) :
    Kp (clob ++ ([.x19] : List Reg)) s t :=
  ⟨fun r hr => h.gpr r (fun hc => hr (List.mem_append_left _ hc))
    (fun hc => hr (List.mem_append_right _ (by simp [hc]))),h.rd,h.wr⟩

theorem savedBits {base : Addr} {m m' : Mem}
    (hf : Frame [VG.Proof.X25519.AArch64.bitsArea base] m m') {i : Nat} (hi : i < 6) :
    word m' base (8*i) = word m base (8*i) := by
  apply BitVec.eq_of_toNat_eq
  have hh := VG.Proof.X25519.AArch64.save_frame (b := base) (k := i) hf (fun r hr => by
    rw [List.mem_singleton.mp hr]; exact VG.Proof.X25519.AArch64.saveR_disj _ (by decide) (by decide)) hi
  simpa only [VG.Proof.X25519.AArch64.wd, VG.Impl.X25519.AArch64.SAVE, Nat.zero_add] using hh

theorem savedInitial {base : Addr} {m : Mem} {g : Reg → BitVec 64}
    (h : ∀ i < 6, VG.Proof.X25519.AArch64.wd m base (VG.Impl.X25519.AArch64.SAVE+8*i) =
      (g (VG.Impl.X25519.AArch64.saved.getD i .x19)).toNat) {i : Nat} (hi : i < 6) :
    word m base (8*i) = g (VG.Impl.X25519.AArch64.saved.getD i .x19) := by
  apply BitVec.eq_of_toNat_eq
  simpa only [VG.Proof.X25519.AArch64.wd, VG.Impl.X25519.AArch64.SAVE, Nat.zero_add] using h i hi

theorem setup_ok {base sc pt : Addr} {s : State} (hs : Sc base s)
    (hn : base.toNat+4096 ≤ 2^64) (h1 : s.gpr .x1 = sc) (h2 : s.gpr .x2 = pt)
    (hsr : (⟨sc,32⟩ : Region) ∈ s.rd) (hpr : (⟨pt,32⟩ : Region) ∈ s.rd)
    (hdS : (⟨sc,32⟩ : Region).Disjoint ⟨base,4096⟩)
    (hdP : (⟨pt,32⟩ : Region).Disjoint ⟨base,4096⟩) :
    WP isa (.block VG.Impl.X25519.AArch64.Word.setup) s fun t =>
      Scratch t base ∧ Good (env t.mem base) (toFe (decodeUCoordinate (bytesAt s.mem pt 32)))
        (init (toFe (decodeUCoordinate (bytesAt s.mem pt 32)))) ∧
      word t.mem base 768 = 0 ∧ t.gpr .x1 = s.gpr .x0 ∧
      (∀ i < 255, t.mem (off base (bitOffset+i)) = BitVec.ofNat 8 (bit (decodeScalar25519 (bytesAt s.mem sc 32)) i)) ∧
      (∀ i < 6, word t.mem base (8*i) = s.gpr (VG.Impl.X25519.AArch64.saved.getD i .x19)) ∧
      Kp (clob ++ ([.x0,.x1,.x19] : List Reg)) s t := by
  rw [VG.Impl.X25519.AArch64.Word.setup]
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.AArch64.save_ok hs) fun a ⟨sv,fa,ka⟩ => ?_
  have hsa := hs.of_kp ka (by decide)
  have fsa : ∀ r ∈ [VG.Proof.X25519.AArch64.saveR base], Region.Sub r (VG.Proof.X25519.AArch64.scR base) := by
    intro r hr; rw [List.mem_singleton.mp hr]; exact Region.sub_of_ble rfl
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.AArch64.bits_ok hsa
    (by rw [ka.gpr _ (by simp),h1])
    (fun i hi => ⟨_,List.mem_append_left _ (ka.rd ▸ hsr),Offset.contains_base sc (by omega) (by omega)⟩)
    (fun i hi r hr => by
      rw [List.mem_singleton.mp hr]
      exact hdS.sub_right (VG.Proof.X25519.AArch64.sub_scR base (d := VG.Impl.X25519.AArch64.BITS) (n := 256) (by decide)) _
        (Offset.contains_base sc (by omega) (by omega)))) fun b ⟨bb,fb,kb⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (base_ok (hsa.of_kp kb (by decide)) hn) fun c ⟨hsc,oc,wc,kc,fc⟩ => ?_
  have fsc := outside_frame fc (by decide)
  have fsb : ∀ r ∈ [VG.Proof.X25519.AArch64.bitsArea base], Region.Sub r (VG.Proof.X25519.AArch64.scR base) := by
    intro r hr; rw [List.mem_singleton.mp hr]; exact VG.Proof.X25519.AArch64.sub_scR _ (by decide)
  have bp : bytesAt c.mem pt 32 = bytesAt s.mem pt 32 := by
    rw [VG.Proof.X25519.AArch64.bytesAt_out fsc (by simp only [List.mem_singleton,forall_eq]; exact Region.sub_of_ble rfl) hdP,
      VG.Proof.X25519.AArch64.bytesAt_out fb fsb hdP,
      VG.Proof.X25519.AArch64.bytesAt_out fa fsa hdP]
  change WP isa (.block ((loadY ++ store4 (offset 0)) ++
    (fieldCode [.copy 3 0,.const 1 1,.const 2 0,.const 4 1,.const 18 121665] ++
    ([.movz .x .x2 0 0, VG.Impl.Ed25519.AArch64.st .x2 768] : List Instr)))) c _
  rw [WP.block_append_iff]
  refine WP.mono (decode_ok hsc (by rw [kc.gpr _ (by decide),kb.gpr _ (by decide),ka.gpr _ (by simp),h2])
    (fun d hd => ⟨_,List.mem_append_left _ (by rw [kc.rd,kb.rd,ka.rd]; exact hpr),
      Offset.contains_base pt (by omega) (by omega)⟩)) fun d ⟨kd,xd⟩ => ?_
  rw [bp] at xd
  refine WP.mono (init_ok (kd.scr hsc) xd) fun t ⟨kt,gt,wt⟩ => ?_
  have ft : Outside base 48 728 b.mem t.mem :=
    (fc.mono (by decide) (by decide)).trans
      ((kd.mem.mono (by decide) (by decide)).trans (kt.mem.mono (by decide) (by decide)))
  refine ⟨kt.scratch (kd.scr hsc),gt,wt,?_,?_,?_,?_,⟩
  · rw [kt.gpr _ (by decide) (by decide), kd.gpr _ (by decide),oc,
      kb.gpr _ (by decide),ka.gpr _ (by simp)]
  · intro i hi
    rw [ft (off base (bitOffset+i)) (by
      right; rw [ofs_off' base (by have := bitOffset_lt; omega)]; have := bitOffset_lt; change 776 ≤ bitOffset+i; simp only [bitOffset, VG.Impl.X25519.AArch64.Word.BITS, VG.Impl.X25519.AArch64.BITS, VG.Impl.X25519.AArch64.slot, VG.Impl.X25519.AArch64.NSLOT]; omega), bb i (by omega)]
    exact VG.Proof.X25519.AArch64.clampB_eq (fun j hj => VG.Proof.X25519.AArch64.byte_out fa fsa hdS hj) hi
  · intro i hi
    rw [ft.word (Or.inl (by omega)) (by omega), savedBits fb hi]
    exact savedInitial sv hi
  · exact (((ka.trans kb).trans kc).trans
      ((LoopKeep.of_field kd).trans kt).kp).sub (by decide)

end VG.Proof.X25519.AArch64.Word
