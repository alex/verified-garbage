import VerifiedGarbage.Proof.TripleDes.X86_64.BitslicedAvx2.Batch
import VerifiedGarbage.Proof.TripleDes.X86_64.Bitsliced.Ecb

/-!
# Batches of 256 blocks

While at least 256 blocks are left, the AVX2 code runs a batch on the next
256 (`wide_ok`): of the `n` blocks, the first `n - n % 256` become their
encryption or decryption, and `rsi` and `rdx` then point at and count the
`n % 256` left. `rbx`, the one callee-saved register the batches use, is
saved in the scratch buffer and restored.
-/

namespace VG.Proof.TripleDes.X86_64.BitslicedAvx2

open VG VG.X86_64 VG.X86_64.StraightY VG.X86_64.RegUpd VG.Impl.TripleDes.X86_64.BitsliceAvx2
open VG.Spec.TripleDes
open VG.Proof.TripleDes.X86_64.Bitsliced (blockOut wAt wAt_wAt blockAt_frame toNat_ofNat_of_le)

/-- A region disjoint from a nonempty one does not cover the whole address space. -/
theorem len_lt_of_disjoint {r₁ r₂ : Region} (h : r₁.Disjoint r₂) (h2 : 0 < r₂.len) : r₁.len < 2 ^ 64 := by
  by_contra hc
  refine h r₂.base ?_ ?_
  · simp only [Region.Contains]; have := (r₂.base - r₁.base).isLt; omega
  · simp only [Region.Contains, BitVec.sub_self]; simp; omega

/-- What the batches may assume of the state they start in: the scratch
buffer and the `n` blocks of data writable (at offset `o` of a writable
region), the schedule readable, apart from each other. -/
structure WideEnv (s : State) : Prop where
  scratch : scratchR s ∈ s.wr
  data : ∃ r ∈ s.wr, ∃ o : Nat, s.gpr .rsi = r.base + BitVec.ofNat 64 o ∧
    o + 8 * (s.gpr .rdx).toNat ≤ r.len ∧ r.len < 2 ^ 64
  keyIn : ∀ i < 48, InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 (8 * i)) 8
  dataBuf : (⟨s.gpr .rsi, 8 * (s.gpr .rdx).toNat⟩ : Region).Disjoint (scratchR s)
  keyBuf : (⟨s.gpr .rdi, 384⟩ : Region).Disjoint (scratchR s)
  keyData : (⟨s.gpr .rdi, 384⟩ : Region).Disjoint ⟨s.gpr .rsi, 8 * (s.gpr .rdx).toNat⟩
  fit : (s.gpr .rsi).toNat + 8 * (s.gpr .rdx).toNat ≤ 2 ^ 64

theorem WideEnv.len {s : State} (E : WideEnv s) : 8 * (s.gpr .rdx).toNat < 2 ^ 64 :=
  len_lt_of_disjoint E.dataBuf (by simp [scratchR])

/-- The registers the batches change, but for `rsi` and `rdx`. -/
def WideRegs (r : Reg) : Prop := PassRegs r ∧ r ≠ .rsi ∧ r ≠ .rdx

/-- `m` blocks left, a multiple of 256 fewer than `n`, and at least 256. -/
structure WideInv (d : Direction) (s₀ : State) (n m : Nat) (s : State) : Prop where
  ge : 256 ≤ m
  le : m ≤ n
  mod : m % 256 = n % 256
  rdx : s.gpr .rdx = BitVec.ofNat 64 m
  rsi : s.gpr .rsi = wAt (s₀.gpr .rsi) (n - m)
  gpr : ∀ r, WideRegs r → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  done : ∀ b < n - m, blockAt s.mem (wAt (s₀.gpr .rsi) b) =
    blockOut (scheduleAt s₀.mem (s₀.gpr .rdi)) d (blockAt s₀.mem (wAt (s₀.gpr .rsi) b))
  frame : Frame [spillR s₀, ⟨s₀.gpr .rsi, 8 * (n - m)⟩] s₀.mem s.mem

structure WideLoopPost (d : Direction) (s₀ : State) (n : Nat) (s : State) : Prop where
  rdx : s.gpr .rdx = BitVec.ofNat 64 (n % 256)
  rsi : s.gpr .rsi = wAt (s₀.gpr .rsi) (n - n % 256)
  gpr : ∀ r, WideRegs r → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  done : ∀ b < n - n % 256, blockAt s.mem (wAt (s₀.gpr .rsi) b) =
    blockOut (scheduleAt s₀.mem (s₀.gpr .rdi)) d (blockAt s₀.mem (wAt (s₀.gpr .rsi) b))
  frame : Frame [spillR s₀, ⟨s₀.gpr .rsi, 8 * (n - n % 256)⟩] s₀.mem s.mem

theorem WideInv.batchPre {d : Direction} {s₀ : State} {n m : Nat} (E : WideEnv s₀)
    (hn : (s₀.gpr .rdx).toNat = n) {s : State} (h : WideInv d s₀ n m s) : BatchPre s := by
  have hl := E.len
  have hfit := E.fit
  have g : ∀ r, WideRegs r → s.gpr r = s₀.gpr r := h.gpr
  have hc := g .rcx (by simp [WideRegs, PassRegs])
  have hdi := g .rdi (by simp [WideRegs, PassRegs])
  have scr : scratchR s = scratchR s₀ := by simp only [scratchR, hc]
  have hge := h.ge
  have hle := h.le
  have st : Region.Sub (stateR s) ⟨s₀.gpr .rsi, 8 * n⟩ := by
    simp only [stateR, h.rsi, wAt]
    exact Offset.sub_base _ (by omega)
  have dataB : (⟨s₀.gpr .rsi, 8 * n⟩ : Region).Disjoint (scratchR s₀) := hn ▸ E.dataBuf
  refine ⟨⟨by rw [scr, h.wr]; exact E.scratch, ?_, ?_⟩, fun i hi => ⟨?_, ?_, ?_⟩, ?_⟩
  · obtain ⟨r, hr, o, hb, hor, hrl⟩ := E.data
    rw [hn] at hor
    refine Ok.of_off (off := o + 8 * (n - m)) (by rw [h.wr]; exact hr) ?_ ?_ hrl
    · show s.gpr .rsi = _
      rw [h.rsi, wAt, hb, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    · show o + 8 * (n - m) + 32 * 64 ≤ r.len; omega
  · rw [scr]; exact dataB.sub_left st
  · rw [hdi, h.rd, h.wr]; exact E.keyIn i hi
  · rw [hdi, scr]; exact E.keyBuf.sub_left (Offset.sub_base _ (by omega))
  · rw [hdi]
    exact (E.keyData.sub_left (Offset.sub_base _ (by omega))).sub_right (hn ▸ st)
  · rw [hdi]; exact E.keyData.sub_right (hn ▸ st)

theorem loop_ok (d : Direction) {s₀ : State} (E : WideEnv s₀) {n : Nat}
    (hn : (s₀.gpr .rdx).toNat = n) (m : Nat) (s : State) (hs : WideInv d s₀ n m s) :
    WP isa (.loop (batch d) .ae) s (WideLoopPost d s₀ n) := by
  refine WP.loop (M := isa) (WideInv d s₀ n) ?_ m s hs
  intro m s h
  have hl := E.len
  have hge := h.ge
  have hle := h.le
  apply WP.mono (batch_ok d (h.batchPre E hn))
  intro s' q
  let D := s₀.gpr .rsi
  let S := s₀.gpr .rdi
  have g : ∀ r, WideRegs r → s.gpr r = s₀.gpr r := h.gpr
  have hc := g .rcx (by simp [WideRegs, PassRegs])
  have hdi := g .rdi (by simp [WideRegs, PassRegs])
  have spl : spillR s = spillR s₀ := by simp only [spillR, hc]
  have hm : (s.gpr .rdx).toNat = m := by rw [h.rdx]; exact toNat_ofNat_of_le hle (by omega)
  -- the memory written so far
  have frame' : Frame [spillR s₀, ⟨D, 8 * (n - (m - 256))⟩] s₀.mem s'.mem := by
    have f₁ : Frame [spillR s₀, ⟨D, 8 * (n - (m - 256))⟩] s₀.mem s.mem := h.frame.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨spillR s₀, List.mem_cons_self, fun _ h => h⟩
      · exact ⟨⟨D, 8 * (n - (m - 256))⟩, List.mem_cons_of_mem _ List.mem_cons_self,
          Region.sub_prefix (by omega)⟩
    have f₂ : Frame [spillR s₀, ⟨D, 8 * (n - (m - 256))⟩] s.mem s'.mem := q.frame.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨spillR s₀, List.mem_cons_self, by rw [spl]; exact fun _ h => h⟩
      · refine ⟨⟨D, 8 * (n - (m - 256))⟩, List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩
        simp only [stateR, h.rsi, wAt]
        exact Offset.sub_base _ (by omega)
    exact f₁.trans f₂
  have dataB : (⟨D, 8 * n⟩ : Region).Disjoint (scratchR s₀) := hn ▸ E.dataBuf
  have done' : ∀ b < n - (m - 256), blockAt s'.mem (wAt D b) =
      blockOut (scheduleAt s₀.mem S) d (blockAt s₀.mem (wAt D b)) := by
    intro b hb
    by_cases hb' : b < n - m
    · rw [← h.done b hb']
      refine blockAt_frame q.frame fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [spl]
        exact (dataB.sub_left (Offset.sub_base _ (by omega))).sub_right (spill_sub s₀)
      · simp only [stateR, h.rsi, wAt]
        exact Offset.disjoint D (Or.inl (by omega)) (by omega) (by omega)
    · obtain ⟨j, rfl⟩ : ∃ j, b = n - m + j := ⟨b - (n - m), by omega⟩
      have e := q.out j (by omega)
      rw [h.rsi, wAt_wAt, hdi] at e
      rw [e]
      have hK : scheduleAt s.mem S = scheduleAt s₀.mem S :=
        VG.Proof.TripleDes.scheduleAt_eq_of_frame S h.frame fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact E.keyBuf.sub_right (spill_sub s₀)
          · exact (hn ▸ E.keyData).sub_right (Region.sub_prefix (by omega))
      have hB : blockAt s.mem (wAt D (n - m + j)) = blockAt s₀.mem (wAt D (n - m + j)) :=
        blockAt_frame h.frame fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact (dataB.sub_left (Offset.sub_base _ (by omega))).sub_right (spill_sub s₀)
          · exact Offset.disjoint_base D (by omega) (by omega)
      rw [hK, hB]
  have rdx' : s'.gpr .rdx = BitVec.ofNat 64 (m - 256) := by
    rw [q.rdx, h.rdx, show (256 : BitVec 64) = BitVec.ofNat 64 256 from rfl,
      BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) hge]
  have rsi' : s'.gpr .rsi = wAt D (n - (m - 256)) := by
    rw [q.rsi, h.rsi, show (2048 : BitVec 64) = BitVec.ofNat 64 (8 * 256) from rfl, BitVec.add_assoc,
      BitVec.ofNat_add_ofNat]
    have e : ∀ a b : Nat, a = b → D + BitVec.ofNat 64 a = D + BitVec.ofNat 64 b := fun a b h => by rw [h]
    exact e _ _ (by omega)
  have gpr' : ∀ r, WideRegs r → s'.gpr r = s₀.gpr r := fun r hr =>
    (q.gpr r hr.1 hr.2.1 hr.2.2).trans (g r hr)
  have cf' : s'.cf = some (decide (m - 256 < 256)) := by
    rw [q.cf, h.rdx, show (256 : BitVec 64) = BitVec.ofNat 64 256 from rfl,
      BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) hge, toNat_ofNat_of_le (n := n) (by omega) (by omega)]
  by_cases hend : m - 256 < 256
  · left
    have e : m - 256 = n % 256 := by have := h.mod; omega
    refine ⟨by show s'.cf.map (!·) = some false; rw [cf']; simp [hend],
      by rw [rdx', e], by rw [rsi', e], gpr', q.rd.trans h.rd, q.wr.trans h.wr,
      by rw [← e]; exact done', by rw [← e]; exact frame'⟩
  · right
    refine ⟨by show s'.cf.map (!·) = some true; rw [cf']; simp [hend], m - 256, by omega,
      ⟨by omega, by omega, by have := h.mod; omega, rdx', rsi', gpr', q.rd.trans h.rd,
        q.wr.trans h.wr, done', frame'⟩⟩

/-! ## The whole phase -/

structure WidePost (d : Direction) (s s' : State) : Prop where
  rdx : s'.gpr .rdx = BitVec.ofNat 64 ((s.gpr .rdx).toNat % 256)
  rsi : s'.gpr .rsi = wAt (s.gpr .rsi) ((s.gpr .rdx).toNat - (s.gpr .rdx).toNat % 256)
  gpr : ∀ r, WideRegs r → s'.gpr r = s.gpr r
  rbx : s'.gpr .rbx = s.gpr .rbx
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  done : ∀ b < (s.gpr .rdx).toNat - (s.gpr .rdx).toNat % 256, blockAt s'.mem (wAt (s.gpr .rsi) b) =
    blockOut (scheduleAt s.mem (s.gpr .rdi)) d (blockAt s.mem (wAt (s.gpr .rsi) b))
  frame : Frame [scratchR s, ⟨s.gpr .rsi, 8 * ((s.gpr .rdx).toNat - (s.gpr .rdx).toNat % 256)⟩]
    s.mem s'.mem

theorem ea_rbxSave (s : State) : s.ea rbxSave = s.gpr .rcx + BitVec.ofNat 64 1016 := rfl

/-- Where `rbx` is saved. -/
def rbxR (s : State) : Region := ⟨s.gpr .rcx + BitVec.ofNat 64 1016, 8⟩

theorem rbx_sub (s : State) : Region.Sub (rbxR s) (scratchR s) := Offset.sub_base _ (by decide)

theorem rbx_spill (s : State) : (rbxR s).Disjoint (spillR s) :=
  Offset.disjoint_base _ (by decide) (by decide)

theorem rbxSave_in (s : State) : (scratchR s).Contains (s.ea rbxSave) 8 :=
  rbx_sub s |> fun h => Offset.contains_base _ (by decide) (by decide)

theorem wide_ok (d : Direction) {s : State} (E : WideEnv s) : WP isa (wide d) s (WidePost d s) := by
  let n := (s.gpr .rdx).toNat
  have hl := E.len
  rw [wide]
  apply WP.seq
  let s₁ := cmpState s .rdx 256
  refine WP.of_runBlock ⟨s₁, cmp_run s .rdx 256, ?_⟩
  have cf₁ : isa.eval .b s₁ = some (decide (n < 256)) := by
    show s₁.cf = _
    simp only [s₁, cmpState, cf_arithFlags, show ((256 : BitVec 32).signExtend 64).toNat = 256 by decide]
    rfl
  apply WP.ite (decide (n < 256)) cf₁
  · intro hlt
    have hlt' : n < 256 := by simpa using hlt
    apply WP.block_nil
    have e : n % 256 = n := Nat.mod_eq_of_lt hlt'
    refine ⟨?_, ?_, fun r _ => by simp [s₁, cmpState], by simp [s₁, cmpState],
      by simp [s₁, cmpState, rd_arithFlags], by simp [s₁, cmpState, wr_arithFlags],
      fun b hb => by simp only [n] at e; omega, ?_⟩
    · simp only [s₁, cmpState, gpr_arithFlags]
      rw [show (s.gpr .rdx).toNat % 256 = (s.gpr .rdx).toNat from e]; simp
    · simp only [s₁, cmpState, gpr_arithFlags]
      rw [show (s.gpr .rdx).toNat - (s.gpr .rdx).toNat % 256 = 0 by simp only [n] at e; omega]
      simp [wAt]
    · simp only [s₁, cmpState, mem_arithFlags]; exact Frame.refl _ _
  · intro hge
    have hge' : 256 ≤ n := by simp at hge; omega
    -- save rbx
    apply WP.seq
    have hst : InRegions s₁.wr (s₁.ea rbxSave) 8 := by
      have := rbxSave_in s
      simp only [s₁, cmpState, wr_arithFlags]
      exact ⟨_, E.scratch, by simpa [s₁, cmpState, State.ea] using this⟩
    let s₂ : State := { s₁ with mem := s₁.mem.writeW (s₁.ea rbxSave) (s₁.gpr .rbx) }
    refine WP.of_runBlock ⟨s₂, by
      rw [runBlock_cons]
      simp only [exec, State.store64, hst, ite_true, runStep_some, runBlock_nil]; rfl, ?_⟩
    have g₂ : s₂.gpr = s.gpr := by simp [s₂, s₁, cmpState]
    have rd₂ : s₂.rd = s.rd := by simp [s₂, s₁, cmpState, rd_arithFlags]
    have wr₂ : s₂.wr = s.wr := by simp [s₂, s₁, cmpState, wr_arithFlags]
    have ea₂ : s₂.ea rbxSave = s.ea rbxSave := by simp [s₂, s₁, cmpState, State.ea]
    have f₂ : Frame [rbxR s] s.mem s₂.mem := by
      simp only [s₂, s₁, cmpState, mem_arithFlags]
      exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
        (by simp only [State.ea, gpr_arithFlags]; exact Region.contains_self _ _)
    have E₂ : WideEnv s₂ := by
      have sc : scratchR s₂ = scratchR s := by simp only [scratchR, g₂]
      refine ⟨by rw [sc, wr₂]; exact E.scratch, by rw [g₂, wr₂]; exact E.data,
        by rw [g₂, rd₂, wr₂]; exact E.keyIn, by rw [g₂, sc]; exact E.dataBuf,
        by rw [g₂, sc]; exact E.keyBuf, by rw [g₂]; exact E.keyData, by rw [g₂]; exact E.fit⟩
    apply WP.seq
    have hn₂ : (s₂.gpr .rdx).toNat = n := by rw [g₂]
    have I : WideInv d s₂ n n s₂ := ⟨hge', Nat.le_refl _, rfl, by rw [g₂]; simp [n], by simp [wAt],
      fun _ _ => rfl, rfl, rfl, fun b hb => by omega, by rw [Nat.sub_self]; exact Frame.refl _ _⟩
    apply WP.mono (loop_ok d E₂ hn₂ n s₂ I)
    intro s₃ p₃
    -- restore rbx
    have c₃ : s₃.gpr .rcx = s.gpr .rcx := (p₃.gpr .rcx (by simp [WideRegs, PassRegs])).trans (by rw [g₂])
    have ea₃ : s₃.ea rbxSave = s.ea rbxSave := by simp [State.ea, rbxSave, c₃]
    have hld : InRegions (s₃.rd ++ s₃.wr) (s₃.ea rbxSave) 8 := by
      rw [ea₃, p₃.wr, wr₂]
      exact ⟨_, List.mem_append_right _ E.scratch, rbxSave_in s⟩
    have saved : s₃.mem.readW (s.ea rbxSave) 64 = s.gpr .rbx := by
      have e₁ : s₃.mem.readW (s.ea rbxSave) 64 = s₂.mem.readW (s.ea rbxSave) 64 := by
        refine p₃.frame.readW (r := rbxR s) (Region.contains_self _ _) ?_ (by decide)
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · simp only [spillR, g₂]; exact rbx_spill s
        · rw [g₂]
          exact (E.dataBuf.sub_left (Region.sub_prefix (by omega))).symm.sub_left (rbx_sub s)
      rw [e₁]
      simp only [s₂, ea₂.symm]
      exact Mem.readW_writeW_self _ _ 8 _ (by decide)
    let s₄ := s₃.setReg .rbx (s₃.mem.readW (s₃.ea rbxSave) 64)
    let s₅ := VOp.vzeroupper.exec s₄
    refine WP.of_runBlock ⟨s₅, by
      rw [runBlock_cons]
      simp only [exec, readSrc, State.load64, hld, ite_true, Option.map_some, runStep_some,
        runBlock_cons]
      rfl, ?_⟩
    have g₅ : ∀ r, r ≠ .rbx → s₅.gpr r = s₃.gpr r := by
      intro r hr; simp [s₅, s₄, gpr_setReg, hr]
    refine ⟨by rw [g₅ _ (by decide), p₃.rdx], by rw [g₅ _ (by decide), p₃.rsi, g₂],
      fun r hr => by rw [g₅ r (by simp only [WideRegs, PassRegs] at hr; exact hr.1.2.1), p₃.gpr r hr, g₂],
      by simp [s₅, s₄, gpr_setReg, ea₃, saved],
      by simp [s₅, s₄, rd_setReg, p₃.rd, rd₂], by simp [s₅, s₄, wr_setReg, p₃.wr, wr₂],
      fun b hb => ?_, ?_⟩
    · have e := p₃.done b hb
      have hm : s₅.mem = s₃.mem := by simp [s₅, s₄, mem_setReg]
      rw [hm]
      simp only [g₂] at e
      rw [e]
      have hK : scheduleAt s₂.mem (s.gpr .rdi) = scheduleAt s.mem (s.gpr .rdi) :=
        VG.Proof.TripleDes.scheduleAt_eq_of_frame _ f₂ fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact E.keyBuf.sub_right (rbx_sub s)
      have hB : blockAt s₂.mem (wAt (s.gpr .rsi) b) = blockAt s.mem (wAt (s.gpr .rsi) b) :=
        blockAt_frame f₂ fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact (E.dataBuf.sub_left (Offset.sub_base _ (by omega))).sub_right (rbx_sub s)
      rw [hK, hB]
    · have hm : s₅.mem = s₃.mem := by simp [s₅, s₄, mem_setReg]
      rw [hm]
      have a : Frame [scratchR s, ⟨s.gpr .rsi, 8 * (n - n % 256)⟩] s.mem s₂.mem :=
        f₂.sub fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact ⟨scratchR s, List.mem_cons_self, rbx_sub s⟩
      have b : Frame [scratchR s, ⟨s.gpr .rsi, 8 * (n - n % 256)⟩] s₂.mem s₃.mem :=
        p₃.frame.sub fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact ⟨scratchR s, List.mem_cons_self, by
              simp only [spillR, g₂]; exact spill_sub s⟩
          · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, by rw [g₂]; exact fun _ h => h⟩
      exact a.trans b

end VG.Proof.TripleDes.X86_64.BitslicedAvx2
