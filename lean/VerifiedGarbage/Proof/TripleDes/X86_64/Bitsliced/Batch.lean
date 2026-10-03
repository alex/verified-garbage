import VerifiedGarbage.Proof.TripleDes.X86_64.Bitsliced.Passes
import VerifiedGarbage.Proof.TripleDes.X86_64.Bitsliced.BatchIO
import VerifiedGarbage.Proof.TripleDes.X86_64.Bitsliced.Bytes
import VerifiedGarbage.Proof.TripleDes.Core

/-!
# A batch

A batch of `k = min(n, 64)` blocks is copied into the state words,
transposed (lane `b` is then IP of block `b`), put through the three
passes, transposed back and copied out: each block becomes its TDEA
encryption or decryption (`batch_ok`).
-/

namespace VG.Proof.TripleDes.X86_64.Bitsliced

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.TripleDes.X86_64.Bitslice VG.Spec.TripleDes
open VG.Proof.TripleDes.Bitslice (ipLane transposeW)

/-- What ECB does to one block. -/
def blockOut (K : Schedule) : Direction → Block → Block
  | .encrypt => encryptBlock K
  | .decrypt => decryptBlock K

theorem ipLane_congr {w : Nat} {W W' : Nat → BitVec w} (hW : ∀ x < 64, W x = W' x) (b : Nat) :
    ipLane W b = ipLane W' b := by
  apply BitVec.eq_of_getLsbD_eq
  intro t ht
  rw [VG.Proof.TripleDes.Bitslice.ipLane_bit _ _ ht, VG.Proof.TripleDes.Bitslice.ipLane_bit _ _ ht,
    hW _ (VG.Proof.TripleDes.Bitslice.ipWord_lt t ht)]

/-! ## The data words -/

theorem DataOk.congr {s s' : State} {D : Addr} {k : Nat} (h : DataOk s D k)
    (hc : s'.gpr .rcx = s.gpr .rcx) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : DataOk s' D k where
  read := by rw [hrd, hwr]; exact h.read
  write := by rw [hwr]; exact h.write
  sep := by simp only [scratchR, hc]; exact h.sep
  fit := h.fit

theorem DataOk.mono {s : State} {D : Addr} {k n : Nat} (h : DataOk s D n) (hk : k ≤ n) :
    DataOk s D k where
  read i hi := h.read i (by omega)
  write i hi := h.write i (by omega)
  sep := h.sep.sub_left (Region.sub_prefix (by omega))
  fit := by have := h.fit; omega

theorem word_sub {D : Addr} {b k : Nat} (hb : b < k) :
    Region.Sub ⟨wAt D b, 8⟩ ⟨D, 8 * k⟩ :=
  Offset.sub_base D (by omega)

/-- A data word of the batch is unchanged by writes to the scratch buffer. -/
theorem DataOk.readW {s : State} {D : Addr} {k : Nat} (h : DataOk s D k) {b : Nat} (hb : b < k)
    {m m' : Mem} (hf : Frame [scratchR s] m m') : m'.readW (wAt D b) 64 = m.readW (wAt D b) 64 :=
  hf.readW (r := ⟨wAt D b, 8⟩) (Region.contains_self _ _)
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact h.sep.sub_left (word_sub hb))
    (by decide)

/-! ## Transposing -/

theorem state_toScratch {s : State} {m m' : Mem} (h : Frame [stateR s] m m') :
    Frame [scratchR s] m m' :=
  h.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨scratchR s, List.mem_singleton_self _, Region.sub_prefix (by decide)⟩

theorem transpose_ok' {s : State} (h : Room s) :
    ∃ s', runBlock isa transpose s = some s' ∧ (∀ j < 64, words s' j = transposeW (words s) j) ∧
      (∀ x < 128, 72 ≤ x → sl s' x = sl s x) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.gpr .rcx = s.gpr .rcx ∧ s'.gpr .rsp = s.gpr .rsp ∧ Frame [scratchR s] s.mem s'.mem := by
  obtain ⟨s', run, w, rd, wr, c, sp, f⟩ := transpose_ok h
  refine ⟨s', run, w, fun x hx hl => ?_, rd, wr, c, sp, state_toScratch f⟩
  simp only [sl, c]
  refine f.readW (r := ⟨Straight.wordAddr (s.gpr .rcx) x, 8⟩) (Region.contains_self _ _) ?_ (by decide)
  intro r hr
  simp only [List.mem_singleton] at hr; subst hr
  exact Offset.disjoint_base (s.gpr .rcx) (d := 8 * x) (n := 8) (k := 576) (by omega) (by omega)

/-! ## The batch -/

/-- What a batch needs: the scratch buffer, a block left, the batch's data
words, and the schedule's words, readable and apart from the scratch buffer. -/
structure BatchPre (s : State) : Prop where
  room : Room s
  pos : 1 ≤ (sl s leftSlot).toNat
  data : DataOk s (sl s dataSlot) (min (sl s leftSlot).toNat 64)
  sched : ∀ i < 48, Apart s (sl s schedSlot + BitVec.ofNat 64 (8 * i))
  schedSep : (⟨sl s schedSlot, 384⟩ : Region).Disjoint (scratchR s)

structure BatchPost (d : Direction) (s : State) (k : Nat) (s' : State) : Prop where
  rcx : s'.gpr .rcx = s.gpr .rcx
  rsp : s'.gpr .rsp = s.gpr .rsp
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  out : ∀ b < k, blockAt s'.mem (wAt (sl s dataSlot) b) =
    blockOut (scheduleAt s.mem (sl s schedSlot)) d (blockAt s.mem (wAt (sl s dataSlot) b))
  data : sl s' dataSlot = wAt (sl s dataSlot) k
  left : sl s' leftSlot = sl s leftSlot - BitVec.ofNat 64 k
  zf : s'.zf = some (sl s leftSlot - BitVec.ofNat 64 k == 0)
  sched : sl s' schedSlot = sl s schedSlot
  saved : ∀ x < 78, 72 ≤ x → sl s' x = sl s x
  frame : Frame [scratchR s, ⟨sl s dataSlot, 8 * k⟩] s.mem s'.mem

/-- The result of a block, from the three passes between IP and FP. -/
theorem blockOut_cores (K : Schedule) (d : Direction) (B : Block) :
    blockOut K d B = encodeBlock (permute fp (match d with
      | .encrypt => VG.Proof.TripleDes.desCore (componentSchedule K 2) .encrypt
          (VG.Proof.TripleDes.desCore (componentSchedule K 1) .decrypt
            (VG.Proof.TripleDes.desCore (componentSchedule K 0) .encrypt (permute ip (decodeBlock B))))
      | .decrypt => VG.Proof.TripleDes.desCore (componentSchedule K 0) .decrypt
          (VG.Proof.TripleDes.desCore (componentSchedule K 1) .encrypt
            (VG.Proof.TripleDes.desCore (componentSchedule K 2) .decrypt
              (permute ip (decodeBlock B)))))) := by
  cases d
  · exact VG.Proof.TripleDes.encryptBlock_eq_cores K B
  · exact VG.Proof.TripleDes.decryptBlock_eq_cores K B

theorem frame_into {rs : List Region} {m m' : Mem} {r : Region} (h : Frame [r] m m') (hr : r ∈ rs) :
    Frame rs m m' :=
  h.mono fun r' h' => by simp only [List.mem_singleton] at h'; subst h'; exact hr

theorem batch_ok (d : Direction) {s : State} (h : BatchPre s) :
    WP isa (batch d) s (BatchPost d s (min (sl s leftSlot).toNat 64)) := by
  have hpos := h.pos
  generalize hk : min (sl s leftSlot).toNat 64 = k
  have hk1 : 1 ≤ k := by omega
  have hk64 : k ≤ 64 := by omega
  have hdata : DataOk s (sl s dataSlot) k := hk ▸ h.data
  let D := sl s dataSlot
  let S := sl s schedSlot
  let L : List Region := [scratchR s, ⟨D, 8 * k⟩]
  have inL : scratchR s ∈ L := List.mem_cons_self
  have dL : (⟨D, 8 * k⟩ : Region) ∈ L := List.mem_cons_of_mem _ List.mem_cons_self
  rw [batch]
  -- the batch's size
  apply WP.seq
  apply WP.mono (batchSize_ok h.room)
  rintro s₁ ⟨bs₁, sl₁, c₁, sp₁, rd₁, wr₁, f₁⟩
  rw [hk] at bs₁
  have h₁ : Room s₁ := h.room.congr c₁ wr₁
  have D₁ : sl s₁ dataSlot = D := sl₁ _ (by decide) (by decide)
  -- the copy in
  apply WP.seq
  apply WP.mono (copyIn_ok h₁ bs₁ hk1 hk64 (by rw [D₁]; exact hdata.congr c₁ rd₁ wr₁))
  rintro s₂ ⟨w₂, sl₂, c₂, sp₂, rd₂, wr₂, f₂⟩
  have h₂ : Room s₂ := h₁.congr c₂ wr₂
  -- the transposition, and the count of passes
  apply WP.seq
  obtain ⟨t₃, run₃, w₃, sl₃, rd₃, wr₃, c₃, sp₃, f₃⟩ := transpose_ok' h₂
  have ht₃ : Room t₃ := h₂.congr c₃ wr₃
  let u₃ := t₃.setReg .rax ((3 : BitVec 32).signExtend 64)
  have hu₃ : Room u₃ := ht₃.congr (by simp [u₃, gpr_setReg]) (by simp [u₃, wr_setReg])
  have e₃ := exec_st (r := Reg.rax) hu₃ (by decide : passSlot < 128)
  let s₃ : State := { u₃ with mem := stMem u₃ passSlot (u₃.gpr .rax) }
  refine WP.of_runBlock ⟨s₃, runBlock_cat_some run₃ (by
    rw [passesStart, runBlock_cons, exec_movImm, runStep_some, runBlock_cons, e₃, runStep_some,
      runBlock_nil]), ?_⟩
  have uc₃ : u₃.gpr .rcx = t₃.gpr .rcx := by simp [u₃, gpr_setReg]
  have c₃' : s₃.gpr .rcx = s₂.gpr .rcx := uc₃.trans c₃
  have slu₃ : ∀ x < 128, sl s₃ x = if x = passSlot then (3 : BitVec 32).signExtend 64 else sl t₃ x := by
    intro x hx
    rw [sl_st u₃ (by decide) _ hx, sl_setReg _ (by decide)]
    simp [u₃, gpr_setReg]
  have h₃ : Room s₃ := hu₃.congr rfl rfl
  have rd₃' : s₃.rd = s₂.rd := by simp [s₃, u₃, rd_setReg, rd₃]
  have wr₃' : s₃.wr = s₂.wr := by simp [s₃, u₃, wr_setReg, wr₃]
  have sp₃' : s₃.gpr .rsp = s₂.gpr .rsp := by simp [s₃, u₃, gpr_setReg, sp₃]
  have f₃' : Frame [scratchR s₂] s₂.mem s₃.mem := by
    have f := stMem_frame (s := u₃) (by decide : passSlot < 128) (u₃.gpr .rax)
    rw [show scratchR u₃ = scratchR s₂ by simp only [scratchR, uc₃, c₃]] at f
    exact f₃.trans (by simpa only [u₃, mem_setReg] using f)
  have words₃ : ∀ j < 64, words s₃ j = transposeW (words s₂) j := by
    intro j hj
    simp only [words]
    have hp : stSlot j ≠ passSlot := by unfold stSlot passSlot; omega
    rw [slu₃ _ (by unfold stSlot; omega)]
    simp only [hp, ↓reduceIte]
    exact w₃ j hj
  have misc₃ : ∀ x < 128, 72 ≤ x → x ≠ passSlot → sl s₃ x = sl s₂ x := by
    intro x hx hl hp
    rw [slu₃ x hx]
    simp only [hp, ↓reduceIte]
    exact sl₃ x hx hl
  -- slots of the batch's start that the passes keep
  have keep₃ : ∀ x < 128, 72 ≤ x → x ≠ batchSlot → x ≠ passSlot → sl s₃ x = sl s x := by
    intro x hx hl hb hp
    rw [misc₃ x hx hl hp, sl₂ x hx hl, sl₁ x hx hb]
  have S₃ : sl s₃ schedSlot = S := keep₃ _ (by decide) (by decide) (by decide) (by decide)
  have cs₃ : s₃.gpr .rcx = s.gpr .rcx := c₃'.trans (c₂.trans c₁)
  have rds₃ : s₃.rd = s.rd := rd₃'.trans (rd₂.trans rd₁)
  have wrs₃ : s₃.wr = s.wr := wr₃'.trans (wr₂.trans wr₁)
  have scr₁ : scratchR s₁ = scratchR s := by simp only [scratchR, c₁]
  have scr₂ : scratchR s₂ = scratchR s := by simp only [scratchR, c₂, c₁]
  have fs₃ : Frame [scratchR s] s.mem s₃.mem := by
    rw [scr₁] at f₂; rw [scr₂] at f₃'
    exact (f₁.trans f₂).trans f₃'
  -- the passes
  apply WP.seq
  have hS₃ : ∀ i < 48, Apart s₃ (sl s₃ schedSlot + BitVec.ofNat 64 (8 * i)) := by
    intro i hi; rw [S₃]; exact (h.sched i hi).congr cs₃ rds₃ wrs₃
  have inv₃ : PassesInv d s₃ 3 s₃ :=
    ⟨h₃, rfl, rfl, rfl, rfl, by decide, by decide, fun _ _ => rfl,
      by rw [slu₃ _ (by decide)]; rfl, fun _ _ _ _ _ _ _ => rfl, Frame.refl _ _⟩
  apply WP.mono (passes_ok d hS₃ 3 s₃ inv₃)
  intro s₄ q₄
  have h₄ : Room s₄ := q₄.room
  -- the transposition back
  apply WP.seq
  obtain ⟨s₅, run₅, w₅, sl₅, rd₅, wr₅, c₅, sp₅, f₅⟩ := transpose_ok' h₄
  refine WP.of_runBlock ⟨s₅, run₅, ?_⟩
  have h₅ : Room s₅ := h₄.congr c₅ wr₅
  have cs₅ : s₅.gpr .rcx = s.gpr .rcx := c₅.trans (q₄.rcx.trans cs₃)
  have rds₅ : s₅.rd = s.rd := rd₅.trans (q₄.rd.trans rds₃)
  have wrs₅ : s₅.wr = s.wr := wr₅.trans (q₄.wr.trans wrs₃)
  have keep₅ : ∀ x < 128, 72 ≤ x → x ≠ keySlot → x ≠ stepSlot → x ≠ roundSlot → x ≠ passSlot →
      sl s₅ x = sl s₃ x := fun x hx hl a b c e => (sl₅ x hx hl).trans (q₄.misc x hx hl a b c e)
  have D₅ : sl s₅ dataSlot = D := by
    rw [keep₅ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      keep₃ _ (by decide) (by decide) (by decide) (by decide)]
  have B₅ : sl s₅ batchSlot = BitVec.ofNat 64 k := by
    rw [keep₅ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      misc₃ _ (by decide) (by decide) (by decide), sl₂ _ (by decide) (by decide), bs₁]
  -- the copy out
  apply WP.seq
  apply WP.mono (copyOut_ok h₅ B₅ hk1 hk64 (by rw [D₅]; exact hdata.congr cs₅ rds₅ wrs₅))
  intro s₆ o₆
  have h₆ : Room s₆ := h₅.congr o₆.rcx o₆.wr
  -- the end
  obtain ⟨s₇, run₇, sch₇, dat₇, left₇, zf₇, oth₇, c₇, sp₇, rd₇, wr₇, f₇⟩ := batchEnd_ok h₆
  refine WP.of_runBlock ⟨s₇, run₇, ?_⟩
  have cs₆ : s₆.gpr .rcx = s.gpr .rcx := o₆.rcx.trans cs₅
  have L₅ : sl s₅ leftSlot = sl s leftSlot := by
    rw [keep₅ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      keep₃ _ (by decide) (by decide) (by decide) (by decide)]
  have diff : s₆.gpr .r10 - s₆.gpr .r11 = sl s leftSlot - BitVec.ofNat 64 k := by
    rw [o₆.r10, o₆.r11, L₅, B₅]
  -- the whole frame
  have frame : Frame L s.mem s₇.mem := by
    have a : Frame L s.mem s₃.mem := frame_into fs₃ inL
    have b : Frame L s₃.mem s₄.mem := by
      have := q₄.frame; simp only [scratchR, cs₃] at this; exact frame_into this inL
    have c : Frame L s₄.mem s₅.mem := by
      have := f₅; simp only [scratchR, q₄.rcx, cs₃] at this; exact frame_into this inL
    have e : Frame L s₅.mem s₆.mem := by
      have := o₆.frame; rw [D₅] at this; exact frame_into this dL
    have g : Frame L s₆.mem s₇.mem := by
      have := f₇; simp only [scratchR, cs₆] at this; exact frame_into this inL
    exact (((a.trans b).trans c).trans e).trans g
  refine ⟨c₇.trans cs₆, sp₇.trans (o₆.rsp.trans (sp₅.trans (q₄.rsp.trans (sp₃'.trans
    (sp₂.trans sp₁))))), rd₇.trans (o₆.rd.trans rds₅), wr₇.trans (o₆.wr.trans wrs₅), ?_,
    by rw [dat₇, o₆.rsi, D₅], by rw [left₇, diff], by rw [zf₇, diff],
    by rw [sch₇, o₆.r8, keep₅ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      S₃],
    fun x hx hl => ?_, frame⟩
  · -- every block of the batch
    intro b hb
    have hb64 : b < 64 := by omega
    let K₃ := scheduleAt s₃.mem (sl s₃ schedSlot)
    have K₃eq : K₃ = scheduleAt s.mem S := by
      simp only [K₃, S₃]
      exact VG.Proof.TripleDes.scheduleAt_eq_of_frame S fs₃ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact h.schedSep)
    -- lane `b` after the first transposition: IP of the block
    have lane₃ : ipLane (words s₃) b = permute ip (decodeBlock (blockAt s.mem (wAt D b))) := by
      rw [ipLane_congr words₃ b]
      refine VG.Proof.TripleDes.Bitslice.ipLane_transpose _ _ hb64 fun j hj => ?_
      simp only [words] at w₂ ⊢
      rw [w₂ b hb, D₁, hdata.readW hb f₁]
      exact readW_bit s.mem (wAt D b) hj
    -- the block's word at the end
    have word₇ : s₇.mem.readW (wAt D b) 64 = transposeW (words s₄) b := by
      have e₇ : s₇.mem.readW (wAt D b) 64 = s₆.mem.readW (wAt D b) 64 := by
        have := (hdata.congr cs₆ (o₆.rd.trans rds₅) (o₆.wr.trans wrs₅)).readW hb f₇
        exact this
      rw [e₇, ← D₅, o₆.data b hb, w₅ b hb64]
    rw [blockOut_cores, ← K₃eq]
    apply blockAt_of_readW
    intro j hj
    rw [word₇, VG.Proof.TripleDes.Bitslice.transpose_out _ _ j hj, ipLane_congr q₄.words b,
      chain_lane d _ _ hb64, lane₃]
    rfl
  · have ne : ∀ y, 78 ≤ y → x ≠ y := fun y hy e => by omega
    rw [oth₇ x (by omega) (ne _ (by decide)) (ne _ (by decide)) (ne _ (by decide)), o₆.slots x (by omega),
      keep₅ x (by omega) hl (ne _ (by decide)) (ne _ (by decide)) (ne _ (by decide)) (ne _ (by decide)),
      keep₃ x (by omega) hl (ne _ (by decide)) (ne _ (by decide))]

end VG.Proof.TripleDes.X86_64.Bitsliced
