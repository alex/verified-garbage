import VerifiedGarbage.Proof.Framework.Arm.Inline
import VerifiedGarbage.Proof.Sha256.Arm.Compress
import VerifiedGarbage.Proof.Sha256.Stream
import VerifiedGarbage.Impl.Sha256.Arm.Stream

/-!
# Streaming SHA-256 on ARMv7: common lemmas

Untrusted: everything here is checked by Lean. Per-instruction WP rules that
expose only what changes, the inlined compression function, saving and
restoring our caller's registers, and arithmetic on 32-bit values.
-/

namespace VG.Proof.Sha256.Arm.Stream

open VG VG.Arm VG.Impl.Sha256.Arm.Stream
open VG.Proof.Sha256.Arm (compress_verified contains_offset)
open VG.Spec.Sha256 (HashValue stateAt blockAt compressBlocks compress parseBlock bytesAt)

/-! ## Regions -/

theorem sub_offset {base : Addr} {off len len' : Nat} (h : off + len ≤ len') (ho : off < 2 ^ 64) :
    Region.Sub ⟨base + BitVec.ofNat 64 off, len⟩ ⟨base, len'⟩ := by
  intro a ha
  simp only [Region.Contains] at *
  have : (a - base).toNat ≤ (a - (base + BitVec.ofNat 64 off)).toNat + off := by
    rw [show a - base = (a - (base + BitVec.ofNat 64 off)) + BitVec.ofNat 64 off by bv_omega,
      BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ho]
    exact Nat.mod_le _ _
  omega

theorem frame_bytes {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {R : Region}
    (hd : ∀ r ∈ rs, R.Disjoint r) (hR : R.len ≤ 2 ^ 64) {i : Nat} (hi : i < R.len) :
    m' (R.base + BitVec.ofNat 64 i) = m (R.base + BitVec.ofNat 64 i) := by
  refine hf _ fun r hr hc => hd r hr _ ?_ hc
  simp only [Region.Contains]
  rw [show R.base + BitVec.ofNat 64 i - R.base = BitVec.ofNat 64 i by bv_omega,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  omega

/-! ## One instruction at a time -/

/-- `s'` is `s` with register `d` set to `v` (the flags aside). -/
structure Upd (s s' : State) (d : Reg) (v : BitVec 32) : Prop where
  gpr : s'.gpr d = v
  other : ∀ r, r ≠ d → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem Upd.setReg (s : State) (d : Reg) (v : BitVec 32) : Upd s (s.setReg d v) d v :=
  ⟨by simp [State.setReg], fun r h => by simp [State.setReg, h], rfl, rfl, rfl, rfl⟩

theorem Upd.subs (s : State) (d : Reg) (x y v : BitVec 32) : Upd s ((subFlags s x y).setReg d v) d v :=
  ⟨by simp [State.setReg], fun r h => by simp [State.setReg, subFlags, h], rfl, rfl, rfl, rfl⟩

/-- `s'` is `s` with memory `m`. -/
structure Mupd (s s' : State) (m : Mem) : Prop where
  gpr : s'.gpr = s.gpr
  mem : s'.mem = m
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

/-- `s'` is `s` with other flags. -/
structure Fupd (s s' : State) : Prop where
  gpr : s'.gpr = s.gpr
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem WP.cons {i : Instr} {is : List Instr} {s s' : State} {Q : State → Prop}
    (h : exec i s = some s') (k : WP isa (.block is) s' Q) : WP isa (.block (i :: is)) s Q :=
  WP.block_cons_iff.mpr ⟨s', h, k⟩

theorem op2_imm {s : State} {v : BitVec 32} (h : encodable v = true) : (Op2.imm v).eval s = some v := by
  simp [Op2.eval, h]

theorem op2_reg (s : State) (r : Reg) : (Op2.reg r).eval s = some (s.gpr r) := rfl

theorem op2_lsr {s : State} {r : Reg} {n : Nat} (h : 1 ≤ n ∧ n ≤ 31) :
    (Op2.shifted r .lsr n).eval s = some (s.gpr r >>> n) := by
  simp [Op2.eval, h]

theorem op2_lsl {s : State} {r : Reg} {n : Nat} (h : 1 ≤ n ∧ n ≤ 31) :
    (Op2.shifted r .lsl n).eval s = some (s.gpr r <<< n) := by
  simp [Op2.eval, h]

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_mov {d : Reg} {o : Op2} {v : BitVec 32} (ho : o.eval s = some v)
    (k : ∀ s', Upd s s' d v → WP isa (.block is) s' Q) : WP isa (.block (.mov d o :: is)) s Q :=
  WP.cons (s' := s.setReg d v) (by simp [exec, ho]) (k _ (Upd.setReg _ _ _))

theorem wp_add {d n : Reg} {o : Op2} {y : BitVec 32} (ho : o.eval s = some y)
    (k : ∀ s', Upd s s' d (s.gpr n + y) → WP isa (.block is) s' Q) :
    WP isa (.block (.dp .add d n o :: is)) s Q :=
  WP.cons (s' := s.setReg d (s.gpr n + y)) (by simp [exec, ho]) (k _ (Upd.setReg _ _ _))

theorem wp_sub {d n : Reg} {o : Op2} {y : BitVec 32} (ho : o.eval s = some y)
    (k : ∀ s', Upd s s' d (s.gpr n - y) → WP isa (.block is) s' Q) :
    WP isa (.block (.dp .sub d n o :: is)) s Q :=
  WP.cons (s' := s.setReg d (s.gpr n - y)) (by simp [exec, ho]) (k _ (Upd.setReg _ _ _))

theorem wp_and {d n : Reg} {o : Op2} {y : BitVec 32} (ho : o.eval s = some y)
    (k : ∀ s', Upd s s' d (s.gpr n &&& y) → WP isa (.block is) s' Q) :
    WP isa (.block (.dp .and d n o :: is)) s Q :=
  WP.cons (s' := s.setReg d (s.gpr n &&& y)) (by simp [exec, ho]) (k _ (Upd.setReg _ _ _))

theorem wp_orr {d n : Reg} {o : Op2} {y : BitVec 32} (ho : o.eval s = some y)
    (k : ∀ s', Upd s s' d (s.gpr n ||| y) → WP isa (.block is) s' Q) :
    WP isa (.block (.dp .orr d n o :: is)) s Q :=
  WP.cons (s' := s.setReg d (s.gpr n ||| y)) (by simp [exec, ho]) (k _ (Upd.setReg _ _ _))

theorem wp_subs {d n : Reg} {o : Op2} {y : BitVec 32} (ho : o.eval s = some y)
    (k : ∀ s', Upd s s' d (s.gpr n - y) → s'.z = (s.gpr n - y == 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.subs d n o :: is)) s Q :=
  WP.cons (s' := (subFlags s (s.gpr n) y).setReg d (s.gpr n - y)) (by simp [exec, ho])
    (k _ (Upd.subs _ _ _ _ _) rfl)

theorem wp_cmp {n : Reg} {o : Op2} {y : BitVec 32} (ho : o.eval s = some y)
    (k : ∀ s', Fupd s s' → s'.z = (s.gpr n - y == 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.cmp n o :: is)) s Q :=
  WP.cons (s' := subFlags s (s.gpr n) y) (by simp [exec, ho]) (k _ ⟨rfl, rfl, rfl, rfl, rfl⟩ rfl)

theorem wp_rev {d m : Reg} (k : ∀ s', Upd s s' d (rev (s.gpr m)) → WP isa (.block is) s' Q) :
    WP isa (.block (.rev d m :: is)) s Q :=
  WP.cons rfl (k _ (Upd.setReg _ _ _))

theorem wp_ldr {t n : Reg} {off : Nat} {a : Addr} (ho : off < 4096)
    (ha : State.addr (s.gpr n + BitVec.ofNat 32 off) = a) (hin : InRegions (s.rd ++ s.wr) a 4)
    (k : ∀ s', Upd s s' t (s.mem.readW a 32) → WP isa (.block is) s' Q) :
    WP isa (.block (.ldr t n off :: is)) s Q := by
  subst ha
  exact WP.cons (exec_ldr ho hin) (k _ (Upd.setReg _ _ _))

theorem wp_str {t n : Reg} {off : Nat} {a : Addr} (ho : off < 4096)
    (ha : State.addr (s.gpr n + BitVec.ofNat 32 off) = a) (hout : InRegions s.wr a 4)
    (k : ∀ s', Mupd s s' (s.mem.writeW a (s.gpr t)) → WP isa (.block is) s' Q) :
    WP isa (.block (.str t n off :: is)) s Q := by
  subst ha
  exact WP.cons (exec_str ho hout) (k _ ⟨rfl, rfl, rfl, rfl, rfl⟩)

theorem wp_ldrb {t n : Reg} {off : Nat} {a : Addr} (ho : off < 4096)
    (ha : State.addr (s.gpr n + BitVec.ofNat 32 off) = a) (hin : InRegions (s.rd ++ s.wr) a 1)
    (k : ∀ s', Upd s s' t ((s.mem a).setWidth 32) → WP isa (.block is) s' Q) :
    WP isa (.block (.ldrb t n off :: is)) s Q := by
  subst ha
  exact WP.cons (s' := s.setReg t ((s.mem _).setWidth 32)) (by simp [exec, ho, State.load8, hin])
    (k _ (Upd.setReg _ _ _))

theorem wp_strb {t n : Reg} {off : Nat} {a : Addr} (ho : off < 4096)
    (ha : State.addr (s.gpr n + BitVec.ofNat 32 off) = a) (hout : InRegions s.wr a 1)
    (k : ∀ s', Mupd s s' (s.mem.writeW a ((s.gpr t).setWidth 8)) → WP isa (.block is) s' Q) :
    WP isa (.block (.strb t n off :: is)) s Q := by
  subst ha
  exact WP.cons (s' := { s with mem := s.mem.writeW _ ((s.gpr t).setWidth 8) })
    (by simp [exec, ho, State.store8, hout]) (k _ ⟨rfl, rfl, rfl, rfl, rfl⟩)

theorem wp_ldrSp {t : Reg} {off : Nat} {a : Addr} (ho : off < 4096)
    (ha : State.addr (s.sp + BitVec.ofNat 32 off) = a) (hin : InRegions (s.rd ++ s.wr) a 4)
    (k : ∀ s', Upd s s' t (s.mem.readW a 32) → WP isa (.block is) s' Q) :
    WP isa (.block (.ldrSp t off :: is)) s Q := by
  subst ha
  exact WP.cons (s' := s.setReg t (s.mem.readW _ 32)) (by simp [exec, ho, State.load32, hin])
    (k _ (Upd.setReg _ _ _))

end

/-! ## The inlined compression function -/

theorem compressBlocks_one (H : HashValue) (m : Mem) (p : Addr) :
    compressBlocks H m p 1 = compress H (blockAt m p) := by
  simp [compressBlocks]

theorem r0_ok : ∀ i ∈ instrs Impl.Sha256.Arm.compress, dstOf i ≠ some .r0 := by
  have : ((instrs Impl.Sha256.Arm.compress).all fun i => dstOf i != some .r0) = true := by
    rw [← Code.allInstrs_eq]; decide +kernel
  intro i hi
  simpa using List.all_eq_true.mp this i hi

theorem r3_ok : ∀ i ∈ instrs Impl.Sha256.Arm.compress, dstOf i ≠ some .r3 := by
  have : ((instrs Impl.Sha256.Arm.compress).all fun i => dstOf i != some .r3) = true := by
    rw [← Code.allInstrs_eq]; decide +kernel
  intro i hi
  simpa using List.all_eq_true.mp this i hi

/-- Compressing the block at `r1` into the hash value at `r0`, with scratch
space at `r3`. -/
theorem compressAt_ok {s : State} {st scr src : BitVec 32}
    (h0 : s.gpr .r0 = st) (h3 : s.gpr .r3 = scr) (h1 : s.gpr .r1 = src)
    (f₀ : st.toNat + 32 ≤ 2 ^ 32) (f₁ : src.toNat + 64 ≤ 2 ^ 32) (f₃ : scr.toNat + 112 ≤ 2 ^ 32)
    (d₁ : Region.Disjoint ⟨State.addr st, 32⟩ ⟨State.addr scr, 112⟩)
    (d₂ : Region.Disjoint ⟨State.addr src, 64⟩ ⟨State.addr st, 32⟩)
    (d₃ : Region.Disjoint ⟨State.addr src, 64⟩ ⟨State.addr scr, 112⟩)
    (hc : Covers [⟨State.addr src, 64⟩, ⟨State.addr st, 32⟩, ⟨State.addr scr, 112⟩] (s.rd ++ s.wr))
    (hw : Covers [⟨State.addr st, 32⟩, ⟨State.addr scr, 112⟩] s.wr) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ preserved, s'.gpr r = s.gpr r) →
      s'.gpr .r0 = st → s'.gpr .r3 = scr → s'.sp = s.sp →
      Frame [⟨State.addr st, 32⟩, ⟨State.addr scr, 112⟩] s.mem s'.mem →
      stateAt s'.mem (State.addr st) =
        compress (stateAt s.mem (State.addr st)) (blockAt s.mem (State.addr src)) → Q s') :
    WP isa compressAt s Q := by
  unfold compressAt
  refine WP.seq (wp_mov (op2_imm (by decide)) fun s₁ u₁ => WP.block_nil ?_)
  have e0 : s₁.gpr .r0 = st := by rw [u₁.other _ (by decide), h0]
  have e1 : s₁.gpr .r1 = src := by rw [u₁.other _ (by decide), h1]
  have e2 : s₁.gpr .r2 = 1 := u₁.gpr
  have e3 : s₁.gpr .r3 = scr := by rw [u₁.other _ (by decide), h3]
  refine WP.inline (k := Proof.Sha256.compressArm) compress_verified.1
    (rd := [⟨State.addr src, 64 * 1⟩]) (wr := [⟨State.addr st, 32⟩, ⟨State.addr scr, 112⟩]) ?_ ?_ ?_ ?_
  · simp only [Proof.Sha256.compressArm, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, e0, e1, e2, e3]
    exact ⟨rfl, trivial, d₁, d₂, d₃, f₀, by simpa using f₁, f₃⟩
  · rw [u₁.rd, u₁.wr]; simpa using hc
  · rw [u₁.wr]; exact hw
  · intro s' hrd hwr habi hf hg hpost
    simp only [Proof.Sha256.compressArm, State.withRegions_gpr, State.withRegions_mem, e0, e1, e2,
      u₁.mem] at hpost
    rw [show (BitVec.toNat (1 : BitVec 32)) = 1 from rfl, compressBlocks_one] at hpost
    refine hQ s' (hrd.trans u₁.rd) (hwr.trans u₁.wr) (fun r hr => ?_) (by rw [hg _ r0_ok, e0])
      (by rw [hg _ r3_ok, e3]) (habi.2.trans u₁.sp) (u₁.mem ▸ hf) hpost
    have : r ≠ .r2 := by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [habi.1 r hr, u₁.other r this]

/-! ## Saving and restoring our caller's registers -/

/-- The memory after storing the registers `l` (values `g`) at `B + offset`. -/
def saveMem (m : Mem) (B : Addr) (g : Reg → BitVec 32) : List (Reg × Nat) → Mem
  | [] => m
  | (r, d) :: l => saveMem (m.writeW (B + BitVec.ofNat 64 d) (g r)) B g l

theorem saveList_ok {b : Reg} {rest : List Instr} (l : List (Reg × Nat)) :
    ∀ (s : State) (Q : State → Prop),
    (∀ p ∈ l, p.2 < 4096 ∧ (s.gpr b).toNat + p.2 < 2 ^ 32 ∧
      InRegions s.wr (State.addr (s.gpr b) + BitVec.ofNat 64 p.2) 4) →
    (∀ s', s'.gpr = s.gpr → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      s'.mem = saveMem s.mem (State.addr (s.gpr b)) s.gpr l → WP isa (.block rest) s' Q) →
    WP isa (.block (l.map (fun p => Instr.str p.1 b p.2) ++ rest)) s Q := by
  induction l with
  | nil => intro s Q _ k; exact k s rfl rfl rfl rfl rfl
  | cons p l ih =>
    intro s Q hl k
    obtain ⟨h1, h2, h3⟩ := hl p (by simp)
    refine wp_str h1 (addr_add h2) h3 fun s₁ u₁ => ?_
    refine ih s₁ Q (fun q hq => ?_) fun s' g rd wr sp m => k s' (g.trans u₁.gpr) (rd.trans u₁.rd)
      (wr.trans u₁.wr) (sp.trans u₁.sp) ?_
    · rw [u₁.gpr, u₁.wr]; exact hl q (List.mem_cons_of_mem _ hq)
    · rw [m, u₁.mem, u₁.gpr]; rfl

theorem save_eq (b : Reg) : save b = saved.map (fun p => Instr.str p.1 b p.2) := rfl

/-- Saving `r4`–`r11` with the scratch pointer in `b`. -/
theorem save_ok {b : Reg} {rest : List Instr} {s : State} {Q : State → Prop}
    (hfit : (s.gpr b).toNat + 160 ≤ 2 ^ 32)
    (hin : ∀ d, 112 ≤ d → d + 4 ≤ 144 → InRegions s.wr (State.addr (s.gpr b) + BitVec.ofNat 64 d) 4)
    (k : ∀ s', s'.gpr = s.gpr → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      s'.mem = saveMem s.mem (State.addr (s.gpr b)) s.gpr saved → WP isa (.block rest) s' Q) :
    WP isa (.block (save b ++ rest)) s Q := by
  rw [save_eq]
  refine saveList_ok saved s Q (fun p hp => ?_) k
  simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  exact ⟨by decide, by simp only; omega, hin _ (by decide) (by decide)⟩

theorem save_sep (B : Addr) {d e : Nat} (hd : d < 2 ^ 32) (he : e < 2 ^ 32)
    (h : d + 4 ≤ e ∨ e + 4 ≤ d) : Mem.Sep (B + BitVec.ofNat 64 d) 4 (B + BitVec.ofNat 64 e) 4 := by
  intro x hx hy
  bv_omega

theorem readW_writeW_save (m : Mem) (B : Addr) (v : BitVec 32) {d e : Nat} (hd : d < 2 ^ 32)
    (he : e < 2 ^ 32) (h : d + 4 ≤ e ∨ e + 4 ≤ d) :
    (m.writeW (B + BitVec.ofNat 64 e) v).readW (B + BitVec.ofNat 64 d) 32 = m.readW (B + BitVec.ofNat 64 d) 32 :=
  Mem.readW_writeW_sep (save_sep B hd he h) (by decide)

set_option simprocs false in
theorem saveMem_saved (m : Mem) (B : Addr) (g : Reg → BitVec 32) :
    ∀ p ∈ saved, (saveMem m B g saved).readW (B + BitVec.ofNat 64 p.2) 32 = g p.1 := by
  intro p hp
  simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp (config := {decide := true}) only [saved, saveMem, Mem.readW_writeW_self32, readW_writeW_save]

theorem saveMem_frame (m : Mem) (B : Addr) (g : Reg → BitVec 32) :
    ∀ (l : List (Reg × Nat)), (∀ p ∈ l, p.2 + 4 ≤ 160) → Frame [⟨B, 160⟩] m (saveMem m B g l) := by
  intro l
  induction l generalizing m with
  | nil => intro _; exact Frame.refl _ _
  | cons p l ih =>
    intro hl
    have h := hl p (by simp)
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (contains_offset (n := 32 / 8) h (by omega))).trans
      (ih _ fun q hq => hl q (List.mem_cons_of_mem _ hq))

theorem saved_bound : ∀ p ∈ saved, p.2 + 4 ≤ 160 ∧ 112 ≤ p.2 := by decide

theorem restoreList_ok {rest : List Instr} (l : List (Reg × Nat)) :
    ∀ (s : State) (Q : State → Prop), (l.map Prod.fst).Nodup →
    (∀ p ∈ l, p.1 ≠ .r3 ∧ p.2 < 4096 ∧ (s.gpr .r3).toNat + p.2 < 2 ^ 32 ∧
      InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r3) + BitVec.ofNat 64 p.2) 4) →
    (∀ s', (∀ p ∈ l, s'.gpr p.1 = s.mem.readW (State.addr (s.gpr .r3) + BitVec.ofNat 64 p.2) 32) →
      (∀ r, r ∉ l.map Prod.fst → s'.gpr r = s.gpr r) → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr →
      s'.sp = s.sp → WP isa (.block rest) s' Q) →
    WP isa (.block (l.map (fun p => Instr.ldr p.1 .r3 p.2) ++ rest)) s Q := by
  induction l with
  | nil => intro s Q _ _ k; exact k s (fun _ h => by cases h) (fun _ _ => rfl) rfl rfl rfl rfl
  | cons p l ih =>
    intro s Q hnd hl k
    obtain ⟨h0, h1, h2, h3⟩ := hl p (by simp)
    simp only [List.map_cons, List.nodup_cons] at hnd
    refine wp_ldr h1 (addr_add h2) h3 fun s₁ u₁ => ?_
    have e3 : s₁.gpr .r3 = s.gpr .r3 := u₁.other _ (Ne.symm h0)
    refine ih s₁ Q hnd.2 (fun q hq => ?_) fun s' hl' ho hm hrd hwr hsp => k s' (fun q hq => ?_)
      (fun r hr => ?_) (hm.trans u₁.mem) (hrd.trans u₁.rd) (hwr.trans u₁.wr) (hsp.trans u₁.sp)
    · rw [e3, u₁.rd, u₁.wr]; exact hl q (List.mem_cons_of_mem _ hq)
    · rcases List.mem_cons.mp hq with rfl | hq
      · rw [ho _ hnd.1, u₁.gpr]
      · rw [hl' q hq, u₁.mem, e3]
    · simp only [List.map_cons, List.mem_cons, not_or] at hr
      rw [ho r hr.2, u₁.other r hr.1]

theorem restore_eq : restore = saved.map (fun p => Instr.ldr p.1 .r3 p.2) := rfl

/-- Restoring `r4`–`r11` from the save area at `scratch`. -/
theorem restore_ok {s : State} {scr : BitVec 32} (h3 : s.gpr .r3 = scr) (hfit : scr.toNat + 160 ≤ 2 ^ 32)
    (hin : ∀ d, 112 ≤ d → d + 4 ≤ 144 → InRegions (s.rd ++ s.wr) (State.addr scr + BitVec.ofNat 64 d) 4)
    (g : Reg → BitVec 32) (hsv : ∀ p ∈ saved, s.mem.readW (State.addr scr + BitVec.ofNat 64 p.2) 32 = g p.1)
    {Q : State → Prop}
    (k : ∀ s', (∀ p ∈ saved, s'.gpr p.1 = g p.1) → (∀ r, r ∉ saved.map Prod.fst → s'.gpr r = s.gpr r) →
      s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp → Q s') :
    WP isa (.block restore) s Q := by
  rw [restore_eq, ← List.append_nil (saved.map _)]
  refine restoreList_ok saved s Q (by decide) (fun p hp => ?_)
    fun s' ho hr hm hrd hwr hsp => WP.block_nil (k s' (fun p hp => ?_) hr hm hrd hwr hsp)
  · simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp
    rw [h3]
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨by decide, by decide, by simp only; omega, hin _ (by decide) (by decide)⟩
  · rw [ho p hp, h3, hsv p hp]

/-! ## Arithmetic -/

theorem bytesAt_getD {m : Mem} {p : Addr} {n : Nat} {l : List Byte} (h : bytesAt m p n = l) {k : Nat}
    (hk : k < n) : m (p + BitVec.ofNat 64 k) = l.getD k 0 := by
  subst h; simp [bytesAt, List.getD_eq_getElem?_getD, hk]

theorem eval_eq (s : State) : eval .eq s = some s.z := rfl
theorem eval_ne (s : State) : eval .ne s = some !s.z := rfl

theorem ofNat_beq_zero {k : Nat} (h : k < 2 ^ 32) : (BitVec.ofNat 32 k == 0) = decide (k = 0) := by
  by_cases hk : k = 0
  · simp [hk]
  · simp only [hk, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro h'
    have := congrArg BitVec.toNat h'
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h] at this
    exact hk this

theorem sub_ofNat {a b : Nat} (h : b ≤ a) :
    BitVec.ofNat 32 a - BitVec.ofNat 32 b = BitVec.ofNat 32 (a - b) := by
  conv_lhs => rw [show a = (a - b) + b by omega, BitVec.ofNat_add]
  rw [BitVec.add_sub_cancel]

theorem sub_beq {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    (BitVec.ofNat 32 a - BitVec.ofNat 32 b == 0) = decide (a = b) := by
  by_cases h : a = b
  · simp [h]
  · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro h'
    apply h
    have := congrArg BitVec.toNat h'
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha,
      Nat.mod_eq_of_lt hb] at this
    change _ = 0 at this
    omega

theorem ofNat_shr {a n : Nat} (h : a < 2 ^ 32) : BitVec.ofNat 32 a >>> n = BitVec.ofNat 32 (a / 2 ^ n) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h, Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.div_le_self _ _) h)]

theorem and63 (x : BitVec 32) : x &&& 63 = BitVec.ofNat 32 (x.toNat % 64) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat]
  rw [show (63 : BitVec 32).toNat = 2 ^ 6 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  omega

end VG.Proof.Sha256.Arm.Stream
