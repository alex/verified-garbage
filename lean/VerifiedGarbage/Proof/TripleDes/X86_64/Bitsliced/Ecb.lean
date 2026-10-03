import VerifiedGarbage.Proof.TripleDes.X86_64.Bitsliced.Batch
import VerifiedGarbage.Proof.Framework.X86_64.Abi

/-!
# The function

After saving the callee-saved registers and its arguments in the scratch
buffer, the function runs batches of up to 64 blocks until none are left
(`loop_ok`), then restores the registers (`ecb_ok`).
-/

namespace VG.Proof.TripleDes.X86_64.Bitsliced

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.TripleDes.X86_64.Bitslice VG.Spec.TripleDes

/-! ## Memory -/

theorem wAt_wAt (D : Addr) (a i : Nat) : wAt (wAt D a) i = wAt D (a + i) := by
  simp only [wAt, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  congr 2; omega

theorem blockAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, (⟨p, 8⟩ : Region).Disjoint r) : blockAt m' p = blockAt m p := by
  apply Vector.ext
  intro i hi
  simp only [blockAt, Vector.getElem_ofFn]
  exact hf.bytes (R := ⟨p, 8⟩) hd (by show 8 ≤ 2 ^ 64; decide) hi

theorem toNat_ofNat_of_le {m n : Nat} (hm : m ≤ n) (hn : 8 * n ≤ 2 ^ 64) :
    (BitVec.ofNat 64 m).toNat = m := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

/-! ## The loop of batches -/

/-- What the loop may assume throughout, of the state it starts in: the
data's `n` blocks at `sl s₀ dataSlot` and the schedule at
`sl s₀ schedSlot`, apart from each other and the scratch buffer. -/
structure BatchesEnv (s₀ : State) (n : Nat) : Prop where
  room : Room s₀
  dataIn : ∀ i < n, InRegions s₀.wr (wAt (sl s₀ dataSlot) i) 8
  dataSep : (⟨sl s₀ dataSlot, 8 * n⟩ : Region).Disjoint (scratchR s₀)
  fit : 8 * n ≤ 2 ^ 64
  keyRead : ∀ i < 48, InRegions (s₀.rd ++ s₀.wr) (sl s₀ schedSlot + BitVec.ofNat 64 (8 * i)) 8
  keySep : (⟨sl s₀ schedSlot, 384⟩ : Region).Disjoint (scratchR s₀)
  keyData : (⟨sl s₀ schedSlot, 384⟩ : Region).Disjoint ⟨sl s₀ dataSlot, 8 * n⟩

/-- `m` blocks left, the first `n - m` done. -/
structure BatchesInv (d : Direction) (s₀ : State) (n m : Nat) (s : State) : Prop where
  rcx : s.gpr .rcx = s₀.gpr .rcx
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  pos : 1 ≤ m
  le : m ≤ n
  left : sl s leftSlot = BitVec.ofNat 64 m
  data : sl s dataSlot = wAt (sl s₀ dataSlot) (n - m)
  sched : sl s schedSlot = sl s₀ schedSlot
  saved : ∀ x < 78, 72 ≤ x → sl s x = sl s₀ x
  done : ∀ b < n - m, blockAt s.mem (wAt (sl s₀ dataSlot) b) =
    blockOut (scheduleAt s₀.mem (sl s₀ schedSlot)) d (blockAt s₀.mem (wAt (sl s₀ dataSlot) b))
  frame : Frame [scratchR s₀, ⟨sl s₀ dataSlot, 8 * (n - m)⟩] s₀.mem s.mem

structure BatchesPost (d : Direction) (s₀ : State) (n : Nat) (s : State) : Prop where
  rcx : s.gpr .rcx = s₀.gpr .rcx
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  saved : ∀ x < 78, 72 ≤ x → sl s x = sl s₀ x
  done : ∀ b < n, blockAt s.mem (wAt (sl s₀ dataSlot) b) =
    blockOut (scheduleAt s₀.mem (sl s₀ schedSlot)) d (blockAt s₀.mem (wAt (sl s₀ dataSlot) b))
  frame : Frame [scratchR s₀, ⟨sl s₀ dataSlot, 8 * n⟩] s₀.mem s.mem

theorem BatchesInv.batchPre {d : Direction} {s₀ : State} {n m : Nat} (E : BatchesEnv s₀ n) {s : State}
    (h : BatchesInv d s₀ n m s) : BatchPre s := by
  have hp := h.pos
  have hl := h.le
  have hm : (sl s leftSlot).toNat = m := by rw [h.left]; exact toNat_ofNat_of_le h.le E.fit
  have scr : scratchR s = scratchR s₀ := by simp only [scratchR, h.rcx]
  refine ⟨E.room.congr h.rcx h.wr, by omega, ?_, fun i hi => ⟨?_, ?_⟩, ?_⟩
  · rw [hm, h.data]
    refine ⟨fun i hi => ?_, fun i hi => ?_, ?_, by omega⟩
    · rw [wAt_wAt, h.rd, h.wr]
      obtain ⟨r, hr, hc⟩ := E.dataIn (n - m + i) (by omega)
      exact ⟨r, List.mem_append_right _ hr, hc⟩
    · rw [wAt_wAt, h.wr]; exact E.dataIn (n - m + i) (by omega)
    · rw [scr]
      exact E.dataSep.sub_left (Offset.sub_base _ (by omega))
  · rw [h.sched, h.rd, h.wr]; exact E.keyRead i hi
  · rw [h.sched, scr]; exact E.keySep.sub_left (Offset.sub_base _ (by omega))
  · rw [h.sched, scr]; exact E.keySep

theorem loop_ok (d : Direction) {s₀ : State} {n : Nat} (E : BatchesEnv s₀ n) (m : Nat) (s : State)
    (hs : BatchesInv d s₀ n m s) : WP isa (.loop (batch d) .ne) s (BatchesPost d s₀ n) := by
  refine WP.loop (M := isa) (BatchesInv d s₀ n) ?_ m s hs
  intro m s h
  have hp := h.pos
  have hl := h.le
  have hfit := E.fit
  apply WP.mono (batch_ok d (h.batchPre E))
  intro s' q
  have hm : (sl s leftSlot).toNat = m := by rw [h.left]; exact toNat_ofNat_of_le h.le E.fit
  rw [hm] at q
  generalize hk : min m 64 = k at q
  have hk1 : 1 ≤ k := by have := h.pos; omega
  have hkm : k ≤ m := by omega
  let D := sl s₀ dataSlot
  let S := sl s₀ schedSlot
  have hD : sl s dataSlot = wAt D (n - m) := h.data
  obtain ⟨qrcx, qrsp, qrd, qwr, qout, qdata, qleft, qzf, qsched, qsaved, qframe⟩ := q
  rw [hD, h.sched] at qout
  rw [hD] at qframe qdata
  have scr : scratchR s = scratchR s₀ := by simp only [scratchR, h.rcx]
  -- the memory written so far
  have frame' : Frame [scratchR s₀, ⟨D, 8 * (n - (m - k))⟩] s₀.mem s'.mem := by
    have f₁ : Frame [scratchR s₀, ⟨D, 8 * (n - (m - k))⟩] s₀.mem s.mem := h.frame.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨scratchR s₀, List.mem_cons_self, fun _ h => h⟩
      · exact ⟨⟨D, 8 * (n - (m - k))⟩, List.mem_cons_of_mem _ List.mem_cons_self,
          Region.sub_prefix (by omega)⟩
    have f₂ : Frame [scratchR s₀, ⟨D, 8 * (n - (m - k))⟩] s.mem s'.mem := qframe.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨scratchR s₀, List.mem_cons_self, by rw [scr]; exact fun _ h => h⟩
      · exact ⟨⟨D, 8 * (n - (m - k))⟩, List.mem_cons_of_mem _ List.mem_cons_self,
          Offset.sub_base _ (by omega)⟩
    exact f₁.trans f₂
  have done' : ∀ b < n - (m - k), blockAt s'.mem (wAt D b) =
      blockOut (scheduleAt s₀.mem S) d (blockAt s₀.mem (wAt D b)) := by
    intro b hb
    by_cases hb' : b < n - m
    · rw [← h.done b hb']
      refine blockAt_frame qframe fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [scr]; exact E.dataSep.sub_left (Offset.sub_base _ (by omega))
      · simp only [wAt]
        exact Offset.disjoint D (Or.inl (by omega)) (by omega) (by omega)
    · obtain ⟨j, rfl⟩ : ∃ j, b = n - m + j := ⟨b - (n - m), by omega⟩
      have e := qout j (by omega)
      rw [wAt_wAt] at e
      rw [e]
      have hK : scheduleAt s.mem S = scheduleAt s₀.mem S :=
        VG.Proof.TripleDes.scheduleAt_eq_of_frame S h.frame fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact E.keySep
          · exact E.keyData.sub_right (Region.sub_prefix (by omega))
      have hB : blockAt s.mem (wAt D (n - m + j)) = blockAt s₀.mem (wAt D (n - m + j)) :=
        blockAt_frame h.frame fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact E.dataSep.sub_left (Offset.sub_base _ (by omega))
          · exact Offset.disjoint_base D (by omega) (by omega)
      rw [hK, hB]
  have left' : sl s' leftSlot = BitVec.ofNat 64 (m - k) := by
    rw [qleft, h.left, BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) hkm]
  have zf' : s'.zf = some (BitVec.ofNat 64 (m - k) == 0) := by
    rw [qzf, h.left, BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) hkm]
  have saved' : ∀ x < 78, 72 ≤ x → sl s' x = sl s₀ x := fun x hx hl =>
    (qsaved x hx hl).trans (h.saved x hx hl)
  have rcx' := qrcx.trans h.rcx
  have rsp' := qrsp.trans h.rsp
  have rd' := qrd.trans h.rd
  have wr' := qwr.trans h.wr
  by_cases hend : m ≤ 64
  · have hkm' : k = m := by omega
    left
    refine ⟨?_, rcx', rsp', rd', wr', saved', ?_, ?_⟩
    · show s'.zf.map (!·) = some false
      rw [zf', hkm', Nat.sub_self]; rfl
    · rw [hkm', Nat.sub_self, Nat.sub_zero] at done'; exact done'
    · rw [hkm', Nat.sub_self, Nat.sub_zero] at frame'; exact frame'
  · have hk64 : k = 64 := by omega
    right
    refine ⟨?_, m - k, by omega, ⟨rcx', rsp', rd', wr', by omega, by omega, left', ?_,
      by rw [qsched, h.sched], saved', done', frame'⟩⟩
    · show s'.zf.map (!·) = some true
      rw [zf']
      have : (BitVec.ofNat 64 (m - k) == 0) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]
        intro h0
        have := congrArg BitVec.toNat h0
        rw [toNat_ofNat_of_le (show m - k ≤ n by have := h.le; omega) E.fit] at this
        have z : (0 : BitVec 64).toNat = 0 := rfl
        omega
      rw [this]; rfl
    · rw [qdata, wAt_wAt]; congr 1; omega

/-! ## Setting up and restoring -/

def setupStores : List (Nat × Reg) :=
  [(72, .rbx), (73, .rbp), (74, .r12), (75, .r13), (76, .r14), (77, .r15),
   (schedSlot, .rdi), (dataSlot, .rsi), (leftSlot, .rdx)]

theorem setup_eq :
    setup = setupStores.map (fun p => st p.1 p.2) ++ ([.alu .cmp .rdx (.imm 0)] : List Instr) := rfl

theorem restore_eq : restore = savedRegs.map (fun p => ld p.1 p.2) := rfl

/-- A block of loads of distinct registers, other than `rcx`, from scratch slots. -/
theorem loads_ok {s : State} (h : Room s) (l : List (Reg × Nat)) (hl : ∀ p ∈ l, p.2 < 128 ∧ p.1 ≠ .rcx)
    (hd : (l.map (·.1)).Nodup) :
    ∃ s', runBlock isa (l.map fun p => ld p.1 p.2) s = some s' ∧ s'.mem = s.mem ∧
      (∀ p ∈ l, s'.gpr p.1 = sl s p.2) ∧ (∀ r, (∀ p ∈ l, p.1 ≠ r) → s'.gpr r = s.gpr r) := by
  induction l generalizing s with
  | nil => exact ⟨s, runBlock_nil, rfl, (fun _ h => by cases h), fun _ _ => rfl⟩
  | cons p l ih =>
    have hp := hl p List.mem_cons_self
    have e := exec_ld h hp.1 p.1
    let s₁ := s.setReg p.1 (sl s p.2)
    have c₁ : s₁.gpr .rcx = s.gpr .rcx := gpr_setReg_of_ne (s := s) _ (Ne.symm hp.2)
    have h₁ : Room s₁ := h.congr c₁ (by simp [s₁, wr_setReg])
    have hn : p.1 ∉ l.map (·.1) := (List.nodup_cons.mp hd).1
    obtain ⟨s', run', m', set', keep'⟩ :=
      ih h₁ (fun q hq => hl q (List.mem_cons_of_mem _ hq)) (List.nodup_cons.mp hd).2
    have sl₁ : ∀ j, sl s₁ j = sl s j := sl_setReg s hp.2 _
    refine ⟨s', ?_, by rw [m']; simp [s₁, mem_setReg], fun q hq => ?_, fun r hr => ?_⟩
    · rw [List.map_cons, runBlock_cons, e, runStep_some]; exact run'
    · rcases List.mem_cons.mp hq with rfl | hq
      · rw [keep' _ (fun r hr he => hn (by rw [← he]; exact List.mem_map_of_mem hr))]
        simp [s₁, gpr_setReg]
      · rw [set' q hq, sl₁]
    · rw [keep' r (fun q hq => hr q (List.mem_cons_of_mem _ hq))]
      simp only [s₁]
      rw [gpr_setReg_of_ne (s := s) _ (Ne.symm (hr p List.mem_cons_self))]

/-! ## The function -/

/-- What the function's contract gives. -/
structure EcbPre (s : State) : Prop where
  rd : s.rd = [⟨s.gpr .rdi, 384⟩]
  wr : s.wr = [⟨s.gpr .rsi, 8 * (s.gpr .rdx).toNat⟩, ⟨s.gpr .rcx, 1024⟩]
  keyData : (⟨s.gpr .rdi, 384⟩ : Region).Disjoint ⟨s.gpr .rsi, 8 * (s.gpr .rdx).toNat⟩
  keyBuf : (⟨s.gpr .rdi, 384⟩ : Region).Disjoint ⟨s.gpr .rcx, 1024⟩
  dataBuf : (⟨s.gpr .rsi, 8 * (s.gpr .rdx).toNat⟩ : Region).Disjoint ⟨s.gpr .rcx, 1024⟩
  retData : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rsi, 8 * (s.gpr .rdx).toNat⟩
  retBuf : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rcx, 1024⟩
  fit : (s.gpr .rsi).toNat + 8 * (s.gpr .rdx).toNat ≤ 2 ^ 64

theorem ecb_blocks (K : Schedule) (d : Direction) (m m' : Mem) (D : Addr) (n : Nat)
    (h : ∀ b < n, blockAt m' (wAt D b) = blockOut K d (blockAt m (wAt D b))) :
    blocksAt m' D n = Spec.TripleDes.ecb K d (blocksAt m D n) := by
  simp only [blocksAt, Spec.TripleDes.ecb, List.map_map]
  apply List.map_congr_left
  intro b hb
  exact h b (List.mem_range.mp hb)

theorem ecb_ok (d : Direction) {s : State} (h : EcbPre s) :
    WP isa (ecb d) s (fun s' => gprPreserved s s' ∧
      blocksAt s'.mem (s.gpr .rsi) (s.gpr .rdx).toNat =
        Spec.TripleDes.ecb (scheduleAt s.mem (s.gpr .rdi)) d
          (blocksAt s.mem (s.gpr .rsi) (s.gpr .rdx).toNat)) := by
  let n := (s.gpr .rdx).toNat
  let D := s.gpr .rsi
  let S := s.gpr .rdi
  have hroom : Room s := ⟨by rw [h.wr]; exact List.mem_cons_of_mem _ List.mem_cons_self⟩
  rw [Impl.TripleDes.X86_64.Bitslice.ecb]
  -- the setup
  apply WP.seq
  obtain ⟨v, runv, gv, rdv, wrv, -, fv, setv, keepv⟩ := stores_ok hroom setupStores (by decide) (by decide)
  let s₀ := arithFlags v (v.gpr .rdx - (0 : BitVec 32).signExtend 64)
    (decide ((v.gpr .rdx).toNat < ((0 : BitVec 32).signExtend 64).toNat))
    (subOverflow (v.gpr .rdx) ((0 : BitVec 32).signExtend 64) (v.gpr .rdx - (0 : BitVec 32).signExtend 64))
  have e₀ : exec (.alu .cmp .rdx (.imm 0)) v = some s₀ := rfl
  refine WP.of_runBlock ⟨s₀, by
    rw [setup_eq]; exact runBlock_cat_some runv (by rw [runBlock_cons, e₀, runStep_some, runBlock_nil]), ?_⟩
  have g₀ : s₀.gpr = s.gpr := by simp only [s₀, gpr_arithFlags, gv]
  have rd₀ : s₀.rd = s.rd := by simp only [s₀, rd_arithFlags, rdv]
  have wr₀ : s₀.wr = s.wr := by simp only [s₀, wr_arithFlags, wrv]
  have mem₀ : s₀.mem = v.mem := by simp only [s₀, mem_arithFlags]
  have sl₀ : ∀ j, sl s₀ j = sl v j := fun j => sl_arithFlags _ _ _ _ j
  have f₀ : Frame [scratchR s] s.mem s₀.mem := by rw [mem₀]; exact fv
  have scr₀ : scratchR s₀ = scratchR s := by simp only [scratchR, g₀]
  have D₀ : sl s₀ dataSlot = D := by rw [sl₀, setv (dataSlot, .rsi) (by simp [setupStores])]
  have S₀ : sl s₀ schedSlot = S := by rw [sl₀, setv (schedSlot, .rdi) (by simp [setupStores])]
  have L₀ : sl s₀ leftSlot = s.gpr .rdx := by rw [sl₀, setv (leftSlot, .rdx) (by simp [setupStores])]
  have zf₀ : s₀.zf = some (s.gpr .rdx == 0) := by
    simp only [s₀, zf_arithFlags, gv]
    rw [show s.gpr .rdx - BitVec.signExtend 64 (0 : BitVec 32) = s.gpr .rdx by simp]
  have hn : 8 * n ≤ 2 ^ 64 := by have := h.fit; omega
  -- the schedule and the data blocks are as on entry
  have K₀ : scheduleAt s₀.mem S = scheduleAt s.mem S :=
    VG.Proof.TripleDes.scheduleAt_eq_of_frame S f₀ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h.keyBuf
  have B₀ : ∀ b < n, blockAt s₀.mem (wAt D b) = blockAt s.mem (wAt D b) := fun b hb =>
    blockAt_frame f₀ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact h.dataBuf.sub_left (Offset.sub_base _ (by omega))
  -- after the loop (or none), the registers restored
  have finish : ∀ s₂ : State, BatchesPost d s₀ n s₂ →
      WP isa (.block restore) s₂ (fun s' => gprPreserved s s' ∧
        blocksAt s'.mem D n = Spec.TripleDes.ecb (scheduleAt s.mem S) d (blocksAt s.mem D n)) := by
    intro s₂ p
    have h₂ : Room s₂ := (hroom.congr (by rw [p.rcx, g₀]) (by rw [p.wr, wr₀]))
    obtain ⟨s', run', m', set', keep'⟩ := loads_ok h₂ savedRegs (by decide) (by decide)
    refine WP.of_runBlock ⟨s', by rw [restore_eq]; exact run', ?_⟩
    have frame : Frame [scratchR s, ⟨D, 8 * n⟩] s.mem s'.mem := by
      rw [m']
      have := p.frame
      rw [scr₀, D₀] at this
      exact (f₀.mono (by simp)).trans this
    refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
    · have saved : ∀ q ∈ savedRegs, s'.gpr q.1 = s.gpr q.1 := by
        intro q hq
        rw [set' q hq, p.saved q.2 (by revert hq q; decide) (by revert hq q; decide), sl₀]
        refine (setv (q.2, q.1) ?_).trans rfl
        revert hq q; decide
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact saved (.rbx, 72) (by decide)
      · exact saved (.rbp, 73) (by decide)
      · rw [keep' .rsp (by decide), p.rsp, g₀]
      · exact saved (.r12, 74) (by decide)
      · exact saved (.r13, 75) (by decide)
      · exact saved (.r14, 76) (by decide)
      · exact saved (.r15, 77) (by decide)
    · refine frame.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) ?_ (by decide)
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h.retBuf
      · exact h.retData
    · apply ecb_blocks
      intro b hb
      have e := p.done b hb
      rw [D₀, S₀, K₀, B₀ b hb, ← m'] at e
      exact e
  apply WP.seq
  apply WP.ite (s.gpr .rdx == 0) zf₀
  · intro hz
    apply WP.block_nil
    have hn0 : n = 0 := by
      have := congrArg BitVec.toNat (beq_iff_eq.mp hz)
      simpa [n] using this
    refine finish s₀ ⟨rfl, rfl, rfl, rfl, fun _ _ _ => rfl, fun b hb => by omega, ?_⟩
    rw [hn0]; exact Frame.refl _ _
  · intro hz
    have hn1 : 1 ≤ n := by
      have : s.gpr .rdx ≠ 0 := by simpa using hz
      have : (s.gpr .rdx).toNat ≠ 0 := fun e => this (BitVec.eq_of_toNat_eq e)
      omega
    have E : BatchesEnv s₀ n := by
      refine ⟨hroom.congr (by rw [g₀]) wr₀, fun i hi => ?_, ?_, hn, fun i hi => ?_, ?_, ?_⟩
      · rw [wr₀, h.wr, D₀]
        exact ⟨_, List.mem_cons_self, Offset.contains_base _ (by omega) (by omega)⟩
      · rw [D₀, scr₀]; exact h.dataBuf
      · rw [rd₀, wr₀, h.rd, S₀]
        exact ⟨_, List.mem_cons_self, Offset.contains_base _ (by omega) (by omega)⟩
      · rw [S₀, scr₀]; exact h.keyBuf
      · rw [S₀, D₀]; exact h.keyData
    have I : BatchesInv d s₀ n n s₀ := by
      refine ⟨rfl, rfl, rfl, rfl, hn1, Nat.le_refl _, ?_, ?_, rfl, fun _ _ _ => rfl,
        fun b hb => by omega, by rw [Nat.sub_self]; exact Frame.refl _ _⟩
      · rw [L₀]; exact BitVec.eq_of_toNat_eq (by simp [n])
      · rw [Nat.sub_self, wAt_zero]
    exact WP.mono (loop_ok d E n s₀ I) finish

end VG.Proof.TripleDes.X86_64.Bitsliced
