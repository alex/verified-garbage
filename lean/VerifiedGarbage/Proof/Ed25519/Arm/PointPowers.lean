import VerifiedGarbage.Proof.Ed25519.Arm.PointTableAddr

/-! Constructing bounded tables of exact point doublings. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

abbrev TableFrame (b : BitVec 32) (o n : Nat) (m m' : Mem) : Prop :=
  Frame [FA ACC b, ⟨State.addr b + BitVec.ofNat 64 o, n⟩] m m'

theorem TableFrame.mono {b : BitVec 32} {o n o' n' : Nat} {m m' : Mem}
    (h : TableFrame b o n m m') (ho : o' ≤ o) (hn : o + n ≤ o' + n') : TableFrame b o' n' m m' := by
  refine h.sub fun r hm => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl
  · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), Offset.sub _ ho hn⟩

theorem TableFrame.workspace {b : BitVec 32} {o n : Nat} {m m' : Mem}
    (h : Frame [FA ACC b] m m') : TableFrame b o n m m' :=
  h.mono fun r hr => by rw [List.mem_singleton.mp hr]; exact List.mem_cons_self ..

theorem TableFrame.table {b : BitVec 32} {o n : Nat} {m m' : Mem}
    (h : Frame [⟨State.addr b + BitVec.ofNat 64 o, n⟩] m m') : TableFrame b o n m m' :=
  h.mono fun _ hr => List.mem_cons_of_mem _ hr

theorem tablePoint_frame {b : BitVec 32} {m m' : Mem} {rs : List Region} (hf : Frame rs m m')
    {d : Nat} (hd : ∀ r ∈ rs, (⟨State.addr b + BitVec.ofNat 64 d, 128⟩ : Region).Disjoint r) :
    tablePoint m' b d = tablePoint m b d := by
  have he : ∀ i, i + 32 ≤ 128 → tableF m' b (d + i) = tableF m b (d + i) := by
    intro i hi
    refine congrArg VG.Proof.X25519.toFe (packedV_frame hf fun r hm => ?_)
    exact (hd r hm).sub_left (Offset.sub _ (by omega) (by omega))
  have h0 := he 0 (by decide)
  simp only [Nat.add_zero] at h0
  simp only [tablePoint, h0, he 32 (by decide), he 64 (by decide), he 96 (by decide)]

theorem TableFrame.point {b : BitVec 32} {o n : Nat} {m m' : Mem}
    (h : TableFrame b o n m m') {d : Nat} (hd : 1600 ≤ d)
    (hsep : d + 128 ≤ o ∨ o + n ≤ d) (hb : d + 128 ≤ 8192) (hn : o + n ≤ 8192) :
    tablePoint m' b d = tablePoint m b d := by
  refine tablePoint_frame h fun r hm => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl
  · exact Offset.disjoint _ (.inr (by omega)) (by omega) (by decide)
  · exact Offset.disjoint _ hsep (by omega) (by omega)

theorem workspace_tablePoint {b : BitVec 32} {m m' : Mem} (h : Frame [FA ACC b] m m')
    {d : Nat} (hd : 1600 ≤ d) (hb : d + 128 ≤ 8192) : tablePoint m' b d = tablePoint m b d := by
  refine tablePoint_frame h fun r hm => ?_
  rw [List.mem_singleton.mp hm]
  exact Offset.disjoint _ (.inr (by omega)) (by omega) (by decide)

abbrev powersClob : List Reg := [.r10, .r11, .r12] ++ clob

structure PowersKeep (b : BitVec 32) (o n : Nat) (s t : State) : Prop where
  rest : Rest powersClob s t
  frame : TableFrame b o n s.mem t.mem

theorem PowersKeep.refl (b : BitVec 32) (o n : Nat) (s : State) : PowersKeep b o n s s :=
  ⟨Rest.refl _ _, Frame.refl _ _⟩

theorem PowersKeep.ctx {b : BitVec 32} {o n : Nat} {s t : State}
    (h : PowersKeep b o n s t) (hc : Ctx b s) : Ctx b t := hc.of_rest h.rest (by decide)

theorem PowersKeep.trans {b : BitVec 32} {o n : Nat} {s t u : State}
    (h : PowersKeep b o n s t) (k : PowersKeep b o n t u) : PowersKeep b o n s u :=
  ⟨h.rest.trans k.rest, h.frame.trans k.frame⟩

theorem PowersKeep.mono {b : BitVec 32} {o n o' n' : Nat} {s t : State}
    (h : PowersKeep b o n s t) (ho : o' ≤ o) (hn : o + n ≤ o' + n') : PowersKeep b o' n' s t :=
  ⟨h.rest, TableFrame.mono h.frame ho hn⟩

theorem powerBatch_ok {s : State} {b : BitVec 32} (hc : Ctx b s) (hl : AllLim s.mem b)
    (hd : env s.mem b 16 = Spec.Ed25519.d) (batch : Bool) :
    WP isa (powerBatch batch) s fun t => AllLim t.mem b ∧
      point (env t.mem b) 0 1 2 3 = powerPoint (point (env s.mem b) 0 1 2 3) (powerStride batch) ∧
      (∀ i : Slot, 16 ≤ i.val → env t.mem b i = env s.mem b i) ∧ IKeep b s t := by
  cases batch with
  | true => exact double16_ok hc hl hd
  | false =>
    refine WP.mono (pointDouble_ok hc hl hd) fun t ⟨hk, hlt, hv, hh⟩ => ?_
    exact ⟨hlt, hv, hh, IKeep.of_keep hk⟩

theorem powersBody_ok (batch : Bool) {s : State} {b : BitVec 32} (hc : Ctx b s)
    (hl : AllLim s.mem b) (o j count : Nat) (hlo : 1600 ≤ o) (hbound : o + 128 * count ≤ 8192)
    (hj : j < count) (hn : count ≤ 32) (h11 : s.gpr .r11 = BitVec.ofNat 32 j)
    (hd : env s.mem b 16 = Spec.Ed25519.d) :
    WP isa (powersBody o count batch) s fun t => t.gpr .r11 = BitVec.ofNat 32 (j + 1) ∧
      t.z = decide (j + 1 = count) ∧ AllLim t.mem b ∧
      tablePoint t.mem b (o + 128 * j) = point (env s.mem b) 0 1 2 3 ∧
      point (env t.mem b) 0 1 2 3 = powerPoint (point (env s.mem b) 0 1 2 3) (powerStride batch) ∧
      (∀ i : Slot, 16 ≤ i.val → env t.mem b i = env s.mem b i) ∧
      PowersKeep b (o + 128 * j) 128 s t := by
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (tableAddr_ok hc o j (by omega) (by omega) h11) fun t ⟨htp, htr, htm⟩ => ?_
  have hct := hc.of_rest htr (by decide)
  refine WP.mono (pointToTable_ok hct (by rw [htm]; exact hl) htp (by omega) (by omega))
    fun u ⟨hut, huk⟩ => ?_
  have heu : env u.mem b = env s.mem b := (huk.env (by omega) (by omega)).trans
    (congrArg (fun m => env m b) htm)
  refine WP.seq (WP.mono (powerBatch_ok (huk.ctx hct)
    (huk.lim (by omega) (by omega) (by rw [htm]; exact hl)) (by rw [heu]; exact hd) batch)
    fun v ⟨hvl, hvp, hvhi, hvk⟩ => ?_)
  have hvc : v.gpr .r11 = BitVec.ofNat 32 j := by
    rw [hvk.rest.gpr _ (by decide), huk.rest.gpr _ (by decide), htr.gpr _ (by decide), h11]
  refine WP.mono (powersNext_ok v j count hj hn hvc) fun w ⟨hwc, hwz, hwr, hwm⟩ => ?_
  refine ⟨hwc, hwz, by rw [hwm]; exact hvl, ?_, ?_, ?_, ?_⟩
  · rw [hwm, workspace_tablePoint hvk.frame (by omega) (by omega), hut, htm]
  · rw [hwm, hvp, heu]
  · intro i hi
    rw [hwm, hvhi i hi, heu]
  · refine ⟨(htr.mono (by decide)).trans ((huk.rest.mono (by decide)).trans
      ((hvk.rest.mono (by decide)).trans (hwr.mono (by decide)))), ?_⟩
    rw [hwm, ← htm]
    exact (TableFrame.table huk.frame).trans (TableFrame.workspace hvk.frame)

end VG.Proof.Ed25519.Arm
