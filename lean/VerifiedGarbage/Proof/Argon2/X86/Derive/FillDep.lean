import VerifiedGarbage.Proof.Argon2.X86.Derive.FillCall

/-!
# Argon2 on x86 (32-bit): what keeps the filling state, and data-dependent addressing

`FS.keep`: the filling state is kept by steps that keep the parameters, the
position and counter in the locals, the cached address block and the
matrix. `dependentWord_ok`: J₁ and J₂ are the first word of the previous
block.
-/

namespace VG.Proof.Argon2.X86.Derive

open VG VG.X86
open VG.X86.Wp (Upd Mupd Fupd wp_movi wp_mov wp_add wp_addi wp_subi wp_addm wp_cmpi wp_ldm wp_stm)
open VG.Spec.Argon2 (Block blockAt zeroBlock FillState)
open VG.Proof.Argon2.X86 (blk)
open VG.Impl.Argon2.X86.Derive (sliceOff segLenOff indexOff laneOff laneLenOff argOff passOff counterOff
  divisorOff strideOff j1Off j2Off)

/-- The offsets of the locals the filling state is about. -/
abbrev fsOffs : List Nat :=
  [divisorOff, segLenOff, laneLenOff, strideOff, passOff, sliceOff, laneOff, indexOff, counterOff]

theorem FS.keep {s₀ s t : State} {pass slice lane index ctr : Nat} {st : FillState}
    (h : FS s₀ pass slice lane index ctr st s) (it : Inv s₀ t) (hl : ∀ d ∈ fsOffs, lw s₀ t d = lw s₀ s d)
    (hc : blk t.mem (scrP s₀) 6144 = blk s.mem (scrP s₀) 6144)
    (hm : ∀ k < (prm s₀).blocks, blockAt t.mem (matrixCell (memB s₀) k) = blockAt s.mem (matrixCell (memB s₀) k)) :
    FS s₀ pass slice lane index ctr st t := by
  refine ⟨it, Prm.of_lw h.pr fun d hd => hl d (by simp at hd ⊢; omega),
    h.pos.of_lw fun d hd => hl d (by simp at hd ⊢; omega), ?_, Represents.keep h.mem hm⟩
  obtain ⟨c0, c1, c2 | ⟨c3, c4⟩⟩ := h.cache
  · exact ⟨c0, by rw [hl _ (by simp)]; exact c1, .inl c2⟩
  · exact ⟨c0, by rw [hl _ (by simp)]; exact c1, .inr ⟨c3, by rw [hc]; exact c4⟩⟩

theorem FS.of_keep {s₀ s t : State} {pass slice lane index ctr : Nat} {st : FillState}
    (h : FS s₀ pass slice lane index ctr st s) (k : Divide.Keep s t) : FS s₀ pass slice lane index ctr st t :=
  h.keep (h.inv.keep k) (fun d _ => lw_mem k.mem d) (by rw [k.mem]) fun _ _ => by rw [k.mem]

/-- `[B + o + d]` -/
theorem addr_shift (B : BitVec 32) (o d : Nat) : addr (B + BitVec.ofNat 32 o) d = addr B (o + d) := by
  simp only [addr, BitVec.add_assoc, BitVec.ofNat_add_ofNat]

section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- A block of `scratch`. -/
theorem scr_blk (m : Mem) {o : Nat} (ho : o + 1024 ≤ 16384) :
    blk m (scrP s₀) o = blockAt m (scrB s₀ + BitVec.ofNat 64 o) := by
  have := hp.scr_fits
  have e : (scrP s₀ + BitVec.ofNat 32 o).setWidth 64 = scrB s₀ + BitVec.ofNat 64 o := HPrime.setWidth_add (by omega)
  have f : (scrP s₀ + BitVec.ofNat 32 o).toNat + 1024 ≤ 2 ^ 32 := by rw [add_nat (by omega)]; omega
  rw [← e, Proof.Argon2.X86.blockAt_eq f, blk_shift]

/-- A word of the matrix is kept by a store to the locals. -/
theorem mem_loc_store {m : Mem} {d : Nat} (hd : d + 4 ≤ 144) (v : BitVec 32) {a : Addr}
    (ha : (memR s₀).Contains a 4) :
    (m.writeW (addr (E s₀) d) v).readW a 32 = m.readW a 32 :=
  ((Frame.refl [⟨addr (E s₀) d, 4⟩] m).writeW (List.mem_singleton_self _) v (Region.contains_self _ _)).readW
    (r := memR s₀) ha (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (loc_disj hp hd (memR s₀) (by simp)).symm) (by decide)

/-- A store to the locals keeps what the filling state is about, but at the word `d`. -/
theorem FS.store {s t : State} {pass slice lane index ctr : Nat} {st : FillState}
    (h : FS s₀ pass slice lane index ctr st s) (it : Inv s₀ t) {d : Nat} (hd : d + 4 ≤ 144) (ha : d % 4 = 0)
    (hd' : d ∉ fsOffs) {v : BitVec 32} (hm : t.mem = s.mem.writeW (addr (E s₀) d) v) : FS s₀ pass slice lane index ctr st t := by
  have f : Frame [⟨addr (E s₀) d, 4⟩] s.mem t.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) v (Region.contains_self _ _)
  refine h.keep it (fun e he => ?_) ?_ fun k hk => ?_
  · show t.mem.readW (addr (E s₀) e) 32 = s.mem.readW (addr (E s₀) e) 32
    rw [hm]
    simp only [fsOffs, List.mem_cons, List.not_mem_nil, or_false] at he hd'
    have : (e + 4 ≤ d ∨ d + 4 ≤ e) ∧ e + 4 ≤ 236 := by
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [divisorOff, segLenOff, laneLenOff, strideOff, passOff, sliceOff, laneOff, indexOff,
        counterOff] at hd' ⊢ <;> omega
    exact lw_store hp (by omega) this.2 this.1.symm v
  · rw [scr_blk hp t.mem (by decide), scr_blk hp s.mem (by decide)]
    refine blockAt_keep f fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    exact (loc_disj hp hd (scrR s₀) (by simp)).symm.sub_left (Offset.sub_base _ (by omega))
  · refine blockAt_keep f fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    have hk' : k < blocksN s₀ := by rw [hp.blocks]; exact hk
    exact (loc_disj hp hd (memR s₀) (by simp)).symm.sub_left (cell_in_mem hk')

/-- `dependentWord`: J₁ and J₂ are the halves of the previous block's first word. -/
theorem dependentWord_ok {s : State} {pass slice lane index ctr : Nat} {st : FillState}
    (h : FS s₀ pass slice lane index ctr st s) (hl : lane < lanesN s₀) (hs : slice < 4)
    (hi : index < (prm s₀).segmentLen) :
    WP isa Impl.Argon2.X86.Derive.dependentWord s fun t => FS s₀ pass slice lane index ctr st t ∧
      lw s₀ t j2Off ++ lw s₀ t j1Off = (blockAt s.mem (matrixCell (memB s₀) (lane * (prm s₀).laneLen +
        (slice * (prm s₀).segmentLen + index + (prm s₀).laneLen - 1) % (prm s₀).laneLen)))[0] := by
  have hm := hp.mem_fits
  have L8 := laneLen_ge hp
  obtain ⟨cl, cf⟩ := cell_fits hp hl (col := (slice * (prm s₀).segmentLen + index + (prm s₀).laneLen - 1) %
    (prm s₀).laneLen) (Nat.mod_lt _ (by omega))
  unfold Impl.Argon2.X86.Derive.dependentWord
  refine WP.seq ((prevPointer_ok hp h.inv h.pr h.pos hl hs hi).mono fun s₁ ⟨a₁, k₁⟩ => ?_)
  generalize (lane * (prm s₀).laneLen + (slice * (prm s₀).segmentLen + index + (prm s₀).laneLen - 1) %
    (prm s₀).laneLen) = c at cl cf a₁ ⊢
  have h₁ := h.of_keep k₁
  have inP : ∀ o, o + 4 ≤ 1024 → (memR s₀).Contains (addr (memP s₀ + BitVec.ofNat 32 (c * 1024)) o) 4 :=
    fun o ho => by
      rw [addr_shift, addr_eq (by omega)]
      exact Offset.contains_base _ (by omega) (by omega)
  have mW : memR s₀ ∈ s₁.wr := by rw [h₁.inv.wr]; exact mem_mem hp
  have in0 : InRegions (s₁.rd ++ s₁.wr) (addr (memP s₀ + BitVec.ofNat 32 (c * 1024)) 0) 4 :=
    ⟨_, List.mem_append_right _ mW, inP 0 (by decide)⟩
  refine wp_ldm a₁ in0 fun s₂ u₂ => ?_
  have h₂ := h₁.of_keep (Divide.Keep.of_upd u₂ (by simp))
  refine wp_stloc hp h₂.inv (d := j1Off) (by decide) fun s₃ i₃ v₃ o₃ g₃ m₃ => ?_
  have h₃ := h₂.store hp i₃ (d := j1Off) (by decide) (by decide) (by decide) m₃
  refine wp_ldm (by rw [g₃, u₂.other _ (by decide), a₁]) ⟨_, List.mem_append_right _ (by rw [h₃.inv.wr]; exact mem_mem hp),
    inP 4 (by decide)⟩ fun s₄ u₄ => ?_
  have h₄ := h₃.of_keep (Divide.Keep.of_upd u₄ (by simp))
  refine wp_stloc hp h₄.inv (d := j2Off) (by decide) fun t it vt ot gt mt => WP.block_nil ⟨?_, ?_⟩
  · exact h₄.store hp it (d := j2Off) (by decide) (by decide) (by decide) mt
  · rw [vt, ot j1Off (by decide) (by decide), lw_mem u₄.mem, v₃, u₄.gpr, m₃, mem_loc_store hp (by decide) _ (inP 4 (by decide)),
      u₂.mem, u₂.gpr, k₁.mem, cell_blk hp _ cl, Proof.Argon2.X86.Derive.blk_zero, addr_shift, addr_shift,
      Nat.add_zero (c * 1024)]

end


/-- Regions a step of the filling loops may write without changing the filling state. -/
def Outside (s₀ : State) (r : Region) : Prop :=
  r.Disjoint (locR s₀) ∧ r.Disjoint ⟨scrB s₀ + BitVec.ofNat 64 6144, 1024⟩ ∧ r.Disjoint (memR s₀)

section
variable {s₀ : State} (hp : DPre s₀)
include hp

theorem loc_word_sub {d : Nat} (hd : d + 4 ≤ 144) : Region.Sub ⟨addr (E s₀) d, 4⟩ (locR s₀) := by
  have := E_hi hp
  exact sub32 (by rw [loc_addr hp (by omega)]; omega) (by rw [loc_addr hp (by omega)]; omega)

theorem FS.frame {s t : State} {pass slice lane index ctr : Nat} {st : FillState}
    (h : FS s₀ pass slice lane index ctr st s) (it : Inv s₀ t) {rs : List Region} (f : Frame rs s.mem t.mem)
    (ho : ∀ r ∈ rs, Outside s₀ r) : FS s₀ pass slice lane index ctr st t := by
  refine h.keep it (fun d hd => ?_) ?_ fun k hk => ?_
  · have hd' : d + 4 ≤ 144 := by
      simp only [fsOffs, List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact f.readW (r := ⟨addr (E s₀) d, 4⟩) (Region.contains_self _ _)
      (fun r hr => (ho r hr).1.symm.sub_left (loc_word_sub hp hd')) (by decide)
  · rw [scr_blk hp t.mem (by decide), scr_blk hp s.mem (by decide)]
    exact blockAt_keep f fun r hr => (ho r hr).2.1.symm
  · have hk' : k < blocksN s₀ := by rw [hp.blocks]; exact hk
    exact blockAt_keep f fun r hr => (ho r hr).2.2.symm.sub_left (cell_in_mem hk')

theorem outside_scr {o n : Nat} (h : o + n ≤ 6144 ∨ (7168 ≤ o ∧ o + n ≤ 16384)) :
    Outside s₀ ⟨scrB s₀ + BitVec.ofNat 64 o, n⟩ := by
  have sub : Region.Sub ⟨scrB s₀ + BitVec.ofNat 64 o, n⟩ (scrR s₀) := Offset.sub_base _ (by omega)
  refine ⟨(loc_disj' hp (R := scrR s₀) (by simp)).symm.sub_left sub, Offset.disjoint _ (by omega) (by omega)
    (by omega), hp.mem_scr.symm.sub_left sub⟩

theorem outside_call : Outside s₀ (callR s₀) :=
  ⟨(loc_call hp).symm, (call_disj hp (R := scrR s₀) (by simp)).sub_right (Offset.sub_base _ (by decide)),
    call_disj hp (R := memR s₀) (by simp)⟩

end
end VG.Proof.Argon2.X86.Derive
