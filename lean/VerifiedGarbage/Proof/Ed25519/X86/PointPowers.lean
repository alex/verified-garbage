import VerifiedGarbage.Proof.Ed25519.X86.PointTable
import VerifiedGarbage.Impl.Ed25519.X86.PointLoop
import VerifiedGarbage.Proof.Ed25519.X86.Points
import VerifiedGarbage.Proof.Ed25519.X86.PowerEnv
import VerifiedGarbage.Proof.Ed25519.ScalarMul
import VerifiedGarbage.Impl.Ed25519.X86.PointPowers

/-! Merged from `Proof.Ed25519.X86.PointPowersFrame`. -/
section
/-! Merged from `Proof.Ed25519.X86.PointTableAddr`. -/
section
/-! A public table index is multiplied by the point's 128 bytes. -/
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

theorem tableAddr_ok {x : BitVec 32} {s : State} (hc : Ctx x s) (off j : Nat)
    (hj : j < 2 ^ 25) (hb : s.gpr .esi = BitVec.ofNat 32 j) :
    WP isa (.block (tableAddr off)) s fun t =>
      Keep s t ∧ t.mem = s.mem ∧ t.gpr .edx = x + BitVec.ofNat 32 (off + 128 * j) := by
  refine Wp.wp_mov fun s₁ h₁ => Wp.wp_movi fun s₂ h₂ => wp_mul fun s₃ h₃ => ?_
  refine Wp.wp_add fun s₄ h₄ _ => Wp.wp_addi fun s₅ h₅ => Wp.wp_mov fun s₆ h₆ => WP.block_nil ?_
  have hk : Keep s s₆ := (updKeep h₁).trans ((updKeep h₂).trans (h₃.keep.trans
    ((updKeep h₄).trans ((updKeep h₅).trans (updKeep h₆)))))
  have hv : s₃.gpr .eax = BitVec.ofNat 32 (128 * j) := by
    apply BitVec.eq_of_toNat_eq
    change v s₃ .eax = _
    rw [h₃.eax]
    simp only [v, h₂.other .eax (by decide), h₁.gpr, hb, h₂.gpr, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (show j < 2 ^ 32 by omega)]
    exact congrArg (fun n => n % 2 ^ 32) (Nat.mul_comm j 128)
  refine ⟨hk, by rw [h₆.mem, h₅.mem, h₄.mem, h₃.mem, h₂.mem, h₁.mem], ?_⟩
  rw [h₆.gpr, h₅.gpr, h₄.gpr, hv, h₃.other .edi (by decide) (by decide),
    h₂.other .edi (by decide), h₁.other .edi (by decide), hc.edi]
  rw [BitVec.add_comm (BitVec.ofNat 32 (128 * j)) x, BitVec.add_assoc,
    ← BitVec.ofNat_add, Nat.add_comm (128 * j) off]

end VG.Proof.Ed25519.X86
end

/-! Merged from `Proof.Ed25519.X86.PointLoop`. -/
section
/-! Fixed-size batches of powers use exactly the specified point formula. -/
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

theorem doubleBody_ok {x : BitVec 32} {s : State} (hc : Ctx x s) {n : Nat}
    (hn : 1 ≤ n) (hn' : n < 2 ^ 32) (hb : s.gpr .esi = BitVec.ofNat 32 n)
    (hd : env s.mem x 16 = Spec.Ed25519.d) :
    WP isa (.block doubleBody) s fun t =>
      IKeep x s t ∧ t.gpr .esi = BitVec.ofNat 32 (n - 1) ∧
      isa.eval .ne t = some (!decide (n - 1 = 0)) ∧
      point (env t.mem x) 0 1 2 3 =
        Spec.Ed25519.pointAdd (point (env s.mem x) 0 1 2 3) (point (env s.mem x) 0 1 2 3) ∧
      ∀ i : Slot, 16 ≤ i.val → env t.mem x i = env s.mem x i := by
  rw [doubleBody, WP.block_append_iff]
  refine WP.mono (pointDouble_ok hc hd) fun t ⟨ht, pt, high⟩ => ?_
  refine Wp.wp_subi fun u hu _ hz => WP.block_nil ?_
  refine ⟨(IKeep.of_field ht).trans (IKeep.of_counter hu), ?_, ?_, ?_, ?_⟩
  · rw [hu.gpr, ht.keep.esi, hb]; exact Wp.ofNat_pred hn
  · show u.zf.map (!·) = _
    rw [hz, ht.keep.esi, hb, Wp.ofNat_pred hn, Wp.ofNat_beq_zero (by omega_using [hn'])]
    rfl
  · rw [hu.mem]; exact pt
  · rw [hu.mem]; exact high

structure DoubleInv (x : BitVec 32) (s₀ : State) (n : Nat) (s : State) : Prop where
  lo : 1 ≤ n
  hi : n ≤ 16
  keep : IKeep x s₀ s
  counter : s.gpr .esi = BitVec.ofNat 32 n
  value : point (env s.mem x) 0 1 2 3 = powerPoint (point (env s₀.mem x) 0 1 2 3) (16 - n)
  high : ∀ i : Slot, 16 ≤ i.val → env s.mem x i = env s₀.mem x i

theorem double16_ok {x : BitVec 32} {s : State} (hc : Ctx x s)
    (hd : env s.mem x 16 = Spec.Ed25519.d) :
    WP isa double16 s fun t => IKeep x s t ∧
      point (env t.mem x) 0 1 2 3 = powerPoint (point (env s.mem x) 0 1 2 3) 16 ∧
      ∀ i : Slot, 16 ≤ i.val → env t.mem x i = env s.mem x i := by
  refine WP.seq (Wp.wp_movi fun t ht => WP.block_nil ?_)
  refine WP.loop (M := isa) (Inv := DoubleInv x s) ?_ 16 t
    ⟨by decide, by decide, IKeep.of_counter ht, ht.gpr, ?_, ?_⟩
  · intro n u h
    have du : env u.mem x 16 = Spec.Ed25519.d := (h.high 16 (by decide)).trans hd
    refine WP.mono (doubleBody_ok (h.keep.ctx hc) h.lo (by omega_using [h.hi]) h.counter du)
      fun v ⟨kv, bv, zv, pv, high⟩ => ?_
    have kk := h.keep.trans kv
    have pp : point (env v.mem x) 0 1 2 3 =
        powerPoint (point (env s.mem x) 0 1 2 3) (16 - (n - 1)) := by
      exact pv.trans ((congrArg₂ Spec.Ed25519.pointAdd h.value h.value).trans
        (by rw [show 16 - (n - 1) = (16 - n) + 1 by omega_using [h.lo, h.hi]]; rfl))
    have hh : ∀ i : Slot, 16 ≤ i.val → env v.mem x i = env s.mem x i :=
      fun i hi => (high i hi).trans (h.high i hi)
    by_cases hn : n = 1
    · subst n
      exact .inl ⟨by rw [zv]; rfl, kk, pp, hh⟩
    · exact .inr ⟨by rw [zv]; simp only [show n - 1 ≠ 0 by omega_using [hn, h.lo], decide_false]; rfl,
        n - 1, by omega_using [h.lo], by omega_using [hn, h.lo], by omega_using [h.hi], kk, bv, pp, hh⟩
  · rw [ht.mem]; rfl
  · rw [ht.mem]; exact fun _ _ => rfl

end VG.Proof.Ed25519.X86
end

/-! Frames for public counters, arithmetic and point tables. -/
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

def PowersFrame (x : BitVec 32) (o n : Nat) (m m' : Mem) : Prop :=
  Frame [sub x 24 4, sub x 64 864, sub x o n] m m'

structure PowersKeep (x : BitVec 32) (o n : Nat) (s t : State) : Prop where
  edi : t.gpr .edi = s.gpr .edi
  esp : t.gpr .esp = s.gpr .esp
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : PowersFrame x o n s.mem t.mem

theorem PowersKeep.refl (x : BitVec 32) (o n : Nat) (s : State) : PowersKeep x o n s s :=
  ⟨rfl, rfl, rfl, rfl, Frame.refl _ _⟩

theorem PowersKeep.ctx {x : BitVec 32} {o n : Nat} {s t : State}
    (h : PowersKeep x o n s t) (hc : Ctx x s) : Ctx x t := hc.keep h.edi h.wr

theorem PowersKeep.trans {x : BitVec 32} {o n : Nat} {s t u : State}
    (h : PowersKeep x o n s t) (k : PowersKeep x o n t u) : PowersKeep x o n s u :=
  ⟨k.edi.trans h.edi, k.esp.trans h.esp, k.rd.trans h.rd, k.wr.trans h.wr, h.frame.trans k.frame⟩

theorem PowersFrame.mono {x : BitVec 32} {o n o' n' : Nat} {m m' : Mem}
    (h : PowersFrame x o n m m') (hx : x.toNat + 8192 ≤ 2 ^ 32)
    (ho : o' ≤ o) (hn : o + n ≤ o' + n') (hob : o < 8192) : PowersFrame x o' n' m m' := by
  apply h.sub
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨sub x 24 4, by simp, fun _ ha => ha⟩
  · exact ⟨sub x 64 864, by simp, fun _ ha => ha⟩
  · exact ⟨sub x o' n', by simp, sub_sub hx ho hn hob⟩

theorem PowersKeep.mono {x : BitVec 32} {o n o' n' : Nat} {s t : State}
    (h : PowersKeep x o n s t) (hc : Ctx x s)
    (ho : o' ≤ o) (hn : o + n ≤ o' + n') (hob : o < 8192) : PowersKeep x o' n' s t :=
  ⟨h.edi, h.esp, h.rd, h.wr, h.frame.mono hc.fit ho hn hob⟩

theorem PowersKeep.of_ikeep {x : BitVec 32} {s t : State} (h : IKeep x s t) (o n : Nat) :
    PowersKeep x o n s t :=
  ⟨h.edi, h.esp, h.rd, h.wr, h.frame.mono (fun _r hr => List.mem_cons_of_mem _
    (List.mem_cons.mpr (Or.inl (List.mem_singleton.mp hr))))⟩

theorem PowersKeep.of_copy {x : BitVec 32} {o n : Nat} {s t : State} (h : CopyKeep x o n s t) :
    PowersKeep x o n s t :=
  ⟨h.gpr _ (by decide), h.gpr _ (by decide), h.rd, h.wr,
    h.frame.mono (fun _r hr => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr))⟩

theorem PowersKeep.of_counter {x : BitVec 32} {s t : State} (o n : Nat)
    (he : t.gpr .edi = s.gpr .edi) (hs : t.gpr .esp = s.gpr .esp)
    (hr : t.rd = s.rd) (hw : t.wr = s.wr) (hf : Frame [sub x 24 4] s.mem t.mem) :
    PowersKeep x o n s t :=
  ⟨he, hs, hr, hw, hf.mono (fun _r h => List.mem_cons.mpr (Or.inl (List.mem_singleton.mp h)))⟩

theorem workspace_counter {x : BitVec 32} {s t : State} (h : IKeep x s t) (hc : Ctx x s) :
    wd t.mem x 24 = wd s.mem x 24 :=
  wd_frame1 h.frame hc.fit (by decide) (by decide) (Or.inl (by decide))

theorem workspace_table {x : BitVec 32} {s t : State} (h : IKeep x s t) (hc : Ctx x s)
    (o : Nat) (hlo : 928 ≤ o) (ho : o + 128 ≤ 8192) :
    tablePoint t.mem x o = tablePoint s.mem x o :=
  tablePoint_frame hc.fit h.frame (by decide) ho (Or.inr hlo)

theorem PowersFrame.table {x : BitVec 32} {o n a : Nat} {m m' : Mem}
    (h : PowersFrame x o n m m') (hx : x.toNat + 8192 ≤ 2 ^ 32)
    (ho : o + n ≤ 8192) (ha : a + 128 ≤ 8192) (hlo : 928 ≤ a)
    (hsep : a + 128 ≤ o ∨ o + n ≤ a) : tablePoint m' x a = tablePoint m x a := by
  apply table_point_of_words
  intro k hk
  apply wd_frame h
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact sub_disj (by omega) (by omega) (Or.inr (by omega))
  · exact sub_disj (by omega) (by omega) (Or.inr (by omega))
  · exact sub_disj (by omega) (by omega) (by omega)

end VG.Proof.Ed25519.X86
end

/-! Merged from `Proof.Ed25519.X86.PointPowersCounter`. -/
section
/-! The public checkpoint counter occupies bytes24 through27. -/
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86
open VG.Impl.X25519.X86 (sc)

theorem word_sub_eq {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    (BitVec.ofNat 32 a - BitVec.ofNat 32 b == 0) = decide (a = b) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq, BitVec.sub_eq_iff_eq_add]
  rw [show (0 : BitVec 32) + BitVec.ofNat 32 b = BitVec.ofNat 32 b from BitVec.zero_add _]
  constructor
  · intro h
    have ht := congrArg BitVec.toNat h
    simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using ht
  · exact congrArg (BitVec.ofNat 32)

theorem powersLoad_ok {x : BitVec 32} {s : State} (hc : Ctx x s) :
    WP isa (.block [.mov .esi (.mem (sc 24))]) s fun t =>
      IKeep x s t ∧ t.mem = s.mem ∧ t.gpr .esi = wd s.mem x 24 := by
  refine Wp.wp_ldm hc.edi (hc.inRW (by decide) (by decide)) fun t ht => WP.block_nil ?_
  exact ⟨IKeep.of_counter ht, ht.mem, ht.gpr⟩

theorem powersNext_ok {x : BitVec 32} {s : State} (hc : Ctx x s) (j count o n : Nat)
    (hj : j + 1 < 2 ^ 32) (hcount : count < 2 ^ 32) (hv : wd s.mem x 24 = BitVec.ofNat 32 j) :
    WP isa (.block (powersNext count)) s fun t =>
      PowersKeep x o n s t ∧ wd t.mem x 24 = BitVec.ofNat 32 (j + 1) ∧
      isa.eval .ne t = some (!decide (j + 1 = count)) ∧
      Frame [sub x 24 4] s.mem t.mem := by
  refine Wp.wp_ldm hc.edi (hc.inRW (by decide) (by decide)) fun t ht => ?_
  refine Wp.wp_addi fun u hu => ?_
  have eu : u.gpr .esi = BitVec.ofNat 32 (j + 1) := by
    rw [hu.gpr, ht.gpr]
    change wd s.mem x 24 + 1 = _
    rw [hv, BitVec.ofNat_add]; rfl
  have cu := (IKeep.of_counter ht).trans (IKeep.of_counter hu) |>.ctx hc
  refine Wp.wp_stm cu.edi (cu.inW (by decide) (by decide)) fun v hv' => ?_
  refine Wp.wp_cmpi fun w hw _ hz => WP.block_nil ?_
  have hm : w.mem = s.mem.writeW (addr x 24) (BitVec.ofNat 32 (j + 1)) := by
    rw [hw.mem, hv'.mem, hu.mem, ht.mem, eu]
  have fr : Frame [sub x 24 4] s.mem w.mem := by
    rw [hm]
    exact frame_write1 (Frame.refl _ _) hc.fit (by decide) (by decide) (by decide) _
  refine ⟨PowersKeep.of_counter o n ?_ ?_ ?_ ?_ fr, ?_, ?_, fr⟩
  · rw [hw.gpr, hv'.gpr, hu.other .edi (by decide), ht.other .edi (by decide)]
  · rw [hw.gpr, hv'.gpr, hu.other .esp (by decide), ht.other .esp (by decide)]
  · rw [hw.rd, hv'.rd, hu.rd, ht.rd]
  · rw [hw.wr, hv'.wr, hu.wr, ht.wr]
  · rw [hm, wd_write_self]
  · show w.zf.map (!·) = _
    rw [hz, hv'.gpr, eu, word_sub_eq hj hcount]; rfl

theorem powersInit_ok {x : BitVec 32} {s : State} (hc : Ctx x s) (o n : Nat) :
    WP isa (.block [.mov .eax (.imm 0), .store (sc 24) .eax]) s fun t =>
      PowersKeep x o n s t ∧ wd t.mem x 24 = 0 ∧ Frame [sub x 24 4] s.mem t.mem := by
  refine Wp.wp_movi fun t ht => ?_
  have ct := (updKeep ht).ctx hc
  refine Wp.wp_stm ct.edi (ct.inW (by decide) (by decide)) fun u hu => WP.block_nil ?_
  have hm : u.mem = s.mem.writeW (addr x 24) (0 : BitVec 32) := by rw [hu.mem, ht.mem, ht.gpr]
  have hf : Frame [sub x 24 4] s.mem u.mem := by
    rw [hm]; exact frame_write1 (Frame.refl _ _) hc.fit (by decide) (by decide) (by decide) _
  refine ⟨PowersKeep.of_counter o n ?_ ?_ ?_ ?_ hf, ?_, hf⟩
  · rw [hu.gpr, ht.other .edi (by decide)]
  · rw [hu.gpr, ht.other .esp (by decide)]
  · rw [hu.rd, ht.rd]
  · rw [hu.wr, ht.wr]
  · rw [hm, wd_write_self]

theorem counter_env {x : BitVec 32} {m m' : Mem} (hx : x.toNat + 8192 ≤ 2 ^ 32)
    (h : Frame [sub x 24 4] m m') : env m' x = env m x := by
  funext i
  apply congrArg VG.Proof.X25519.toFe
  exact fe_frame1 h hx (by decide) (by simp only [offset]; omega)
    (Or.inr (by simp only [offset]; omega))

end VG.Proof.Ed25519.X86
end

/-! Write the current point, then advance one or sixteen doublings. -/
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

theorem IKeep.of_mem {x : BitVec 32} {s t : State} (h : Keep s t) (hm : t.mem = s.mem) :
    IKeep x s t := ⟨h.edi, h.esp, h.rd, h.wr, by rw [hm]; exact Frame.refl _ _⟩

theorem powerBatch_ok {x : BitVec 32} {s : State} (hc : Ctx x s)
    (hd : env s.mem x 16 = Spec.Ed25519.d) (batch : Bool) :
    WP isa (powerBatch batch) s fun t => IKeep x s t ∧
      point (env t.mem x) 0 1 2 3 = powerPoint (point (env s.mem x) 0 1 2 3) (powerStride batch) ∧
      ∀ i : Slot, 16 ≤ i.val → env t.mem x i = env s.mem x i := by
  cases batch with
  | true => exact double16_ok hc hd
  | false => exact WP.mono (pointDouble_ok hc hd) fun _ ⟨hk, hp, hh⟩ => ⟨IKeep.of_field hk, hp, hh⟩

theorem powersBody_ok {x : BitVec 32} {s : State} (hc : Ctx x s)
    (start count j : Nat) (batch : Bool) (hj : j < count) (hc' : count ≤ 32)
    (hlo : 928 ≤ start) (hfit : start + 128 * count ≤ 8192)
    (hindex : wd s.mem x 24 = BitVec.ofNat 32 j) (hd : env s.mem x 16 = Spec.Ed25519.d) :
    WP isa (powersBody start count batch) s fun t =>
      PowersKeep x (start + 128 * j) 128 s t ∧ wd t.mem x 24 = BitVec.ofNat 32 (j + 1) ∧
      isa.eval .ne t = some (!decide (j + 1 = count)) ∧
      point (env t.mem x) 0 1 2 3 = powerPoint (point (env s.mem x) 0 1 2 3) (powerStride batch) ∧
      tablePoint t.mem x (start + 128 * j) = point (env s.mem x) 0 1 2 3 ∧
      ∀ i : Slot, 16 ≤ i.val → env t.mem x i = env s.mem x i := by
  refine WP.seq (WP.mono (powersLoad_ok hc) fun s₁ ⟨k₁, m₁, b₁⟩ => ?_)
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (tableAddr_ok (k₁.ctx hc) start j (by omega) (b₁.trans hindex)) fun s₂ ⟨k₂, m₂, p₂⟩ => ?_
  have c₂ := k₂.ctx (k₁.ctx hc)
  refine WP.mono (pointToTable_ok c₂ p₂ (by omega) (by omega)) fun s₃ ⟨k₃, p₃⟩ => ?_
  have c₃ := k₃.ctx c₂
  have e₃ : env s₃.mem x = env s.mem x := by
    rw [table_env hc.fit k₃.frame (by omega) (by omega), m₂, m₁]
  have i₃ : wd s₃.mem x 24 = BitVec.ofNat 32 j := by
    rw [wd_frame1 k₃.frame hc.fit (by omega) (by decide) (Or.inl (by omega)), m₂, m₁]
    exact hindex
  have pk₃ : PowersKeep x (start + 128 * j) 128 s s₃ :=
    ((PowersKeep.of_ikeep k₁ _ _).trans
      (PowersKeep.of_ikeep (IKeep.of_mem k₂ m₂) _ _)).trans (PowersKeep.of_copy k₃)
  refine WP.seq (WP.mono (powerBatch_ok c₃ (by rw [e₃]; exact hd) batch) fun s₄ ⟨k₄, p₄, h₄⟩ => ?_)
  refine WP.mono (powersNext_ok (k₄.ctx c₃) j count (start + 128 * j) 128 (by omega) (by omega)
    ((workspace_counter k₄ c₃).trans i₃)) fun s₅ ⟨k₅, i₅, z₅, f₅⟩ => ?_
  have e₅ : env s₅.mem x = env s₄.mem x := counter_env hc.fit f₅
  refine ⟨(pk₃.trans (PowersKeep.of_ikeep k₄ _ _)).trans k₅, i₅, z₅, ?_, ?_, ?_⟩
  · rw [e₅, p₄, e₃]
  · rw [tablePoint_frame hc.fit f₅ (by decide) (by omega) (Or.inr (by omega)),
      workspace_table k₄ c₃ _ (by omega) (by omega), p₃, m₂, m₁]
  · intro i hi
    rw [e₅, h₄ i hi, e₃]

end VG.Proof.Ed25519.X86
