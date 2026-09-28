import VerifiedGarbage.Proof.Sha512.PPC64LE.Compress
import VerifiedGarbage.Proof.Sha512.Stream
import VerifiedGarbage.Proof.Framework.PPC64LE.Inline
import VerifiedGarbage.Impl.Sha512.PPC64LE.Stream

/-!
# Streaming SHA-512 on PPC64LE: common lemmas

Untrusted: everything here is checked by Lean. Weakest-precondition rules for
the instruction forms used, and the inlined compression function
(`compressAt`).
-/

namespace VG.Proof.Sha512.PPC64LE.Stream

open VG VG.PPC64LE VG.Impl.Sha512.PPC64LE.Stream
open VG.Proof.Sha512.PPC64LE (compress_verified)
open VG.Spec.Sha512 (HashValue stateAt blockAt compressBlocks compress parseBlock bytesAt)

/-! ## One instruction at a time -/

/-- `s'` is `s` with register `d` set to `v`. -/
structure Upd (s s' : State) (d : Reg) (v : BitVec 64) : Prop where
  gpr : s'.gpr d = v
  other : ∀ r, r ≠ d → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem Upd.write (s : State) (d : Reg) (v : BitVec 64) : Upd s (s.write d v) d v :=
  ⟨by simp [State.write], fun r h => by simp [State.write, h], rfl, rfl, rfl, rfl⟩

theorem read_one (m : Mem) (a : Addr) : (m.read a 1 : BitVec 8) = m a := by
  simp only [Mem.read]
  ext i hi
  rw [BitVec.getElem_append]
  simp only [show i < 8 by omega, dite_true]

/-- `s'` is `s` with memory `m`. -/
structure Mupd (s s' : State) (m : Mem) : Prop where
  gpr : s'.gpr = s.gpr
  mem : s'.mem = m
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem WP.cons {i : Instr} {is : List Instr} {s s' : State} {Q : State → Prop}
    (h : exec i s = some s') (k : WP isa (.block is) s' Q) : WP isa (.block (i :: is)) s Q :=
  WP.block_cons_iff.mpr ⟨s', h, k⟩

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_addi {d n : Reg} {imm : Nat} (hn : n ≠ .r0) (h : imm < 2 ^ 15)
    (k : ∀ s', Upd s s' d (s.gpr n + BitVec.ofNat 64 imm) → WP isa (.block is) s' Q) :
    WP isa (.block (.addi d n imm :: is)) s Q :=
  WP.cons (exec_addi hn h) (k _ (Upd.write _ _ _))

theorem wp_mov {d n : Reg} (k : ∀ s', Upd s s' d (s.gpr n) → WP isa (.block is) s' Q)
    (hn : n ≠ .r0 := by decide) :
    WP isa (.block (mov d n :: is)) s Q :=
  wp_addi hn (by decide) fun s' u => k s' (by simpa using u)

theorem wp_subi {d n : Reg} {imm : Nat} (hn : n ≠ .r0) (h : imm ≤ 2 ^ 15)
    (k : ∀ s', Upd s s' d (s.gpr n - BitVec.ofNat 64 imm) → WP isa (.block is) s' Q) :
    WP isa (.block (.subi d n imm :: is)) s Q :=
  WP.cons (exec_subi hn h) (k _ (Upd.write _ _ _))

theorem wp_li {d : Reg} {imm : Nat} (h : imm < 2 ^ 15)
    (k : ∀ s', Upd s s' d (BitVec.ofNat 64 imm) → WP isa (.block is) s' Q) :
    WP isa (.block (.li d imm :: is)) s Q :=
  WP.cons (exec_li h) (k _ (Upd.write _ _ _))

theorem wp_add {d n m : Reg}
    (k : ∀ s', Upd s s' d (s.gpr n + s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.add d n m :: is)) s Q :=
  WP.cons exec_add (k _ (Upd.write _ _ _))

theorem wp_sub {d n m : Reg}
    (k : ∀ s', Upd s s' d (s.gpr n - s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.sub d n m :: is)) s Q :=
  WP.cons exec_sub (k _ (Upd.write _ _ _))

theorem wp_and {d n m : Reg}
    (k : ∀ s', Upd s s' d (s.gpr n &&& s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.logic .and d n m :: is)) s Q :=
  WP.cons exec_logic (k _ (Upd.write _ _ _))

theorem wp_lsr {d n : Reg} {sh : Nat} (h : sh < 64)
    (k : ∀ s', Upd s s' d (s.gpr n >>> sh) → WP isa (.block is) s' Q) :
    WP isa (.block (.lsr .d d n sh :: is)) s Q :=
  WP.cons (exec_lsr_d h) (k _ (Upd.write _ _ _))

theorem wp_lbz {t n : Reg} {off : Nat} {a : Addr} (hn : n ≠ .r0) (ho : off < 2 ^ 15)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hin : InRegions (s.rd ++ s.wr) a 1)
    (k : ∀ s', Upd s s' t ((s.mem a).setWidth 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.lbz t n off :: is)) s Q := by
  refine WP.cons (s' := s.write t ((s.mem a).setWidth 64)) ?_ (k _ (Upd.write _ _ _))
  rw [exec_lbz hn ho (by rw [ha]; exact hin), ha, read_one]

theorem wp_stb {t n : Reg} {off : Nat} {a : Addr} (hn : n ≠ .r0) (ho : off < 2 ^ 15)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hout : InRegions s.wr a 1)
    (k : ∀ s', Mupd s s' (s.mem.writeW a ((s.gpr t).setWidth 8)) → WP isa (.block is) s' Q) :
    WP isa (.block (.stb t n off :: is)) s Q := by
  refine WP.cons (s' := { s with mem := s.mem.writeW a ((s.gpr t).setWidth 8) }) ?_
    (k _ ⟨rfl, rfl, rfl, rfl, rfl⟩)
  rw [exec_stb hn ho (by rw [ha]; exact hout), ha]
  rfl

theorem wp_std {t n : Reg} {off : Nat} {a : Addr} (hn : n ≠ .r0) (ho : off < 2 ^ 15 ∧ off % 4 = 0)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hout : InRegions s.wr a 8)
    (k : ∀ s', Mupd s s' (s.mem.writeW a (s.gpr t)) → WP isa (.block is) s' Q) :
    WP isa (.block (.store .d t n off :: is)) s Q := by
  refine WP.cons (s' := { s with mem := s.mem.writeW a (s.gpr t) }) ?_ (k _ ⟨rfl, rfl, rfl, rfl, rfl⟩)
  rw [exec_store_d hn ho (by rw [ha]; exact hout), ha]

theorem wp_stw {t n : Reg} {off : Nat} {a : Addr} (hn : n ≠ .r0) (ho : off < 2 ^ 15)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hout : InRegions s.wr a 4)
    (k : ∀ s', Mupd s s' (s.mem.writeW a ((s.gpr t).setWidth 32)) → WP isa (.block is) s' Q) :
    WP isa (.block (.store .w t n off :: is)) s Q := by
  refine WP.cons (s' := { s with mem := s.mem.writeW a ((s.gpr t).setWidth 32) }) ?_
    (k _ ⟨rfl, rfl, rfl, rfl, rfl⟩)
  rw [exec_store_w hn ho (by rw [ha]; exact hout), ha]

theorem wp_ld {t n : Reg} {off : Nat} {a : Addr} (hn : n ≠ .r0) (ho : off < 2 ^ 15 ∧ off % 4 = 0)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hin : InRegions (s.rd ++ s.wr) a 8)
    (k : ∀ s', Upd s s' t (s.mem.readW a 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.load .d t n off :: is)) s Q := by
  refine WP.cons (s' := s.write t (s.mem.readW a 64)) ?_ (k _ (Upd.write _ _ _))
  rw [exec_load_d hn ho (by rw [ha]; exact hin), ha]

theorem wp_lwz {t n : Reg} {off : Nat} {a : Addr} (hn : n ≠ .r0) (ho : off < 2 ^ 15)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hin : InRegions (s.rd ++ s.wr) a 4)
    (k : ∀ s', Upd s s' t ((s.mem.readW a 32).setWidth 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.load .w t n off :: is)) s Q := by
  refine WP.cons (s' := s.write t ((s.mem.readW a 32).setWidth 64)) ?_ (k _ (Upd.write _ _ _))
  rw [exec_load_w hn ho (by rw [ha]; exact hin), ha]

theorem wp_stwbrx {t n m : Reg} {a : Addr} (hn : n ≠ .r0)
    (ha : s.gpr n + s.gpr m = a) (hout : InRegions s.wr a 4)
    (k : ∀ s', Mupd s s' (s.mem.writeW a (rev32 ((s.gpr t).setWidth 32))) → WP isa (.block is) s' Q) :
    WP isa (.block (.storeRev .w t n m :: is)) s Q := by
  refine WP.cons (s' := { s with mem := s.mem.writeW a (rev32 ((s.gpr t).setWidth 32)) }) ?_
    (k _ ⟨rfl, rfl, rfl, rfl, rfl⟩)
  rw [exec_storeRev_w hn (by rw [ha]; exact hout), ha]

theorem wp_stdbrx {t n m : Reg} {a : Addr} (hn : n ≠ .r0)
    (ha : s.gpr n + s.gpr m = a) (hout : InRegions s.wr a 8)
    (k : ∀ s', Mupd s s' (s.mem.writeW a (rev64 (s.gpr t))) → WP isa (.block is) s' Q) :
    WP isa (.block (.storeRev .d t n m :: is)) s Q := by
  refine WP.cons (s' := { s with mem := s.mem.writeW a (rev64 (s.gpr t)) }) ?_
    (k _ ⟨rfl, rfl, rfl, rfl, rfl⟩)
  rw [exec_storeRev_d hn (by rw [ha]; exact hout), ha]

end

/-! ## The inlined compression function -/

theorem compressBlocks_one (H : HashValue) (m : Mem) (p : Addr) :
    compressBlocks H m p 1 = compress H (blockAt m p) := by
  simp [compressBlocks]

theorem one_toNat : (BitVec.ofNat 64 1).toNat = 1 := rfl

/-- Compressing the block at `r4` into the hash value at `r26`, with scratch
space at `r27`: the callee-saved registers are kept. -/
theorem compressAt_ok {s : State} {st scr src : Addr}
    (h26 : s.gpr .r26 = st) (h27 : s.gpr .r27 = scr) (h4 : s.gpr .r4 = src)
    (d₁ : Region.Disjoint ⟨st, 64⟩ ⟨scr, 176⟩) (d₂ : Region.Disjoint ⟨src, 128⟩ ⟨st, 64⟩)
    (d₃ : Region.Disjoint ⟨src, 128⟩ ⟨scr, 176⟩)
    (hc : Covers [⟨src, 128⟩, ⟨st, 64⟩, ⟨scr, 176⟩] (s.rd ++ s.wr))
    (hw : Covers [⟨st, 64⟩, ⟨scr, 176⟩] s.wr) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ preserved, s'.gpr r = s.gpr r) →
      s'.sp = s.sp → Frame [⟨st, 64⟩, ⟨scr, 176⟩] s.mem s'.mem →
      stateAt s'.mem st = compress (stateAt s.mem st) (blockAt s.mem src) → Q s') :
    WP isa compressAt s Q := by
  unfold compressAt
  refine WP.seq (wp_mov fun s₁ u₁ => wp_li (by decide) fun s₂ u₂ =>
    wp_mov fun s₃ u₃ => WP.block_nil ?_)
  have e3 : s₃.gpr .r3 = st := by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, h26]
  have e4 : s₃.gpr .r4 = src := by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h4]
  have e5 : s₃.gpr .r5 = BitVec.ofNat 64 1 := by
    rw [u₃.other _ (by decide), u₂.gpr]
  have e6 : s₃.gpr .r6 = scr := by
    rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), h27]
  have keep : ∀ r ∈ preserved, s₃.gpr r = s.gpr r := by
    intro r hr
    have : r ≠ .r3 ∧ r ≠ .r5 ∧ r ≠ .r6 := by
      revert r; decide
    rw [u₃.other _ this.2.2, u₂.other _ this.2.1, u₁.other _ this.1]
  have m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  have rd₃ : s₃.rd = s.rd := by rw [u₃.rd, u₂.rd, u₁.rd]
  have wr₃ : s₃.wr = s.wr := by rw [u₃.wr, u₂.wr, u₁.wr]
  have sp₃ : s₃.sp = s.sp := by rw [u₃.sp, u₂.sp, u₁.sp]
  refine WP.inline (k := Proof.Sha512.compressPPC64LE) compress_verified.1
    (rd := [⟨src, 128 * 1⟩]) (wr := [⟨st, 64⟩, ⟨scr, 176⟩]) ?_ ?_ ?_ ?_
  · simp only [Proof.Sha512.compressPPC64LE, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, e3, e4, e5, e6, one_toNat]
    exact ⟨trivial, trivial, d₁, d₂, d₃⟩
  · rw [rd₃, wr₃]; simpa using hc
  · rw [wr₃]; exact hw
  · intro s' hrd hwr habi hf _ hpost
    simp only [Proof.Sha512.compressPPC64LE, State.withRegions_gpr, State.withRegions_mem, e3, e4, e5,
      one_toNat, compressBlocks_one, m₃] at hpost
    exact hQ s' (hrd.trans rd₃) (hwr.trans wr₃) (fun r hr => (habi.1 r hr).trans (keep r hr))
      (habi.2.1.trans sp₃) (m₃ ▸ hf) hpost

/-! ## Arithmetic -/

theorem ofNat_succ (k : Nat) : BitVec.ofNat 64 (k + 1) = BitVec.ofNat 64 k + 1 := by
  rw [BitVec.ofNat_add]; rfl

theorem ofNat_pred {k : Nat} (h : 1 ≤ k) : BitVec.ofNat 64 k - 1 = BitVec.ofNat 64 (k - 1) := by
  rw [show k = (k - 1) + 1 by omega, ofNat_succ, Nat.add_sub_cancel, BitVec.add_sub_cancel]

theorem ofNat_beq_zero {k : Nat} (h : k < 2 ^ 64) : (BitVec.ofNat 64 k == 0) = decide (k = 0) := by
  by_cases hk : k = 0
  · simp [hk]
  · simp only [hk, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro h'
    have := congrArg BitVec.toNat h'
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h] at this
    exact hk this

theorem sub_ofNat {a b : Nat} (h : b ≤ a) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) := by
  conv_lhs => rw [show a = (a - b) + b by omega, BitVec.ofNat_add]
  rw [BitVec.add_sub_cancel]

theorem sub_beq {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a - BitVec.ofNat 64 b == 0) = decide (a = b) := by
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

/-- `x >>> 7`, of a number below 2⁶⁴. -/
theorem ofNat_shr7 {a : Nat} (h : a < 2 ^ 64) : BitVec.ofNat 64 a >>> 7 = BitVec.ofNat 64 (a / 128) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h,
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (by omega)]

theorem bytesAt_getD {m : Mem} {p : Addr} {n : Nat} {l : List Byte} (h : bytesAt m p n = l) {k : Nat}
    (hk : k < n) : m (p + BitVec.ofNat 64 k) = l.getD k 0 := by
  subst h; simp [bytesAt, List.getD_eq_getElem?_getD, hk]

/-- `eval` of the branch conditions. -/
theorem eval_zero (s : State) (r : Reg) : eval (.zero .d r) s = some (s.gpr r == 0) := by
  simp [eval, State.read]

theorem eval_nonzero (s : State) (r : Reg) : eval (.nonzero .d r) s = some (s.gpr r != 0) := by
  simp [eval, State.read]

/-! ## Saving the caller's registers -/

/-- The memory after saving `r26`–`r31` (values `g`) at `b + 176 … b + 216`. -/
def saveMem (m : Mem) (b : Addr) (g : Reg → BitVec 64) : Mem :=
  (((((m.writeW (b + BitVec.ofNat 64 176) (g .r26)).writeW (b + BitVec.ofNat 64 184) (g .r27)).writeW
    (b + BitVec.ofNat 64 192) (g .r28)).writeW (b + BitVec.ofNat 64 200) (g .r29)).writeW
    (b + BitVec.ofNat 64 208) (g .r30)).writeW (b + BitVec.ofNat 64 216) (g .r31)

theorem save_sep (b : Addr) {d e : Nat} (hd : d < 2 ^ 32) (he : e < 2 ^ 32)
    (h : d + 8 ≤ e ∨ e + 8 ≤ d) : Mem.Sep (b + BitVec.ofNat 64 d) 8 (b + BitVec.ofNat 64 e) 8 := by
  intro x hx hy
  bv_omega

theorem readW_writeW_save (m : Mem) (b : Addr) (v : BitVec 64) {d e : Nat} (hd : d < 2 ^ 32)
    (he : e < 2 ^ 32) (h : d + 8 ≤ e ∨ e + 8 ≤ d) :
    (m.writeW (b + BitVec.ofNat 64 e) v).readW (b + BitVec.ofNat 64 d) 64 = m.readW (b + BitVec.ofNat 64 d) 64 :=
  Mem.readW_writeW_sep (save_sep b hd he h) (by decide)

set_option simprocs false in
theorem saveMem_saved (m : Mem) (b : Addr) (g : Reg → BitVec 64) :
    ∀ p ∈ saved, (saveMem m b g).readW (b + BitVec.ofNat 64 p.2) 64 = g p.1 := by
  intro p hp
  simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp (config := {decide := true}) only [saveMem, Mem.readW_writeW_self64, readW_writeW_save]

theorem saveMem_frame (m : Mem) (b : Addr) (g : Reg → BitVec 64) :
    Frame [⟨b, 224⟩] m (saveMem m b g) := by
  have c : ∀ d : Nat, d + 8 ≤ 224 → (⟨b, 224⟩ : Region).Contains (b + BitVec.ofNat 64 d) (64 / 8) :=
    fun d hd => Proof.Sha512.PPC64LE.contains_offset hd (by omega)
  simp only [saveMem]
  exact (((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 176 (by omega))).writeW
    (List.mem_singleton_self _) _ (c 184 (by omega))).writeW (List.mem_singleton_self _) _
    (c 192 (by omega))).writeW (List.mem_singleton_self _) _ (c 200 (by omega))).writeW
    (List.mem_singleton_self _) _ (c 208 (by omega)) |>.writeW (List.mem_singleton_self _) _
    (c 216 (by omega))

theorem save_eq (b : Reg) : save b = [.store .d .r26 b 176, .store .d .r27 b 184,
    .store .d .r28 b 192, .store .d .r29 b 200, .store .d .r30 b 208, .store .d .r31 b 216] := rfl

/-- Saving `r26`–`r31` with the scratch pointer in `b`. -/
theorem save_ok {b : Reg} (hb : b ≠ .r0) {rest : List Instr} {s : State} {Q : State → Prop}
    (hin : ∀ d, 176 ≤ d → d + 8 ≤ 224 → InRegions s.wr (s.gpr b + BitVec.ofNat 64 d) 8)
    (k : ∀ s', s'.gpr = s.gpr → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      s'.mem = saveMem s.mem (s.gpr b) s.gpr → WP isa (.block rest) s' Q) :
    WP isa (.block (save b ++ rest)) s Q := by
  rw [save_eq]
  simp only [List.cons_append, List.nil_append]
  refine wp_std hb (by decide) rfl (hin 176 (by omega) (by omega)) fun s₁ g₁ => ?_
  refine wp_std hb (by decide) (by rw [g₁.gpr]) (by rw [g₁.wr]; exact hin 184 (by omega) (by omega))
    fun s₂ g₂ => ?_
  refine wp_std hb (by decide) (by rw [g₂.gpr, g₁.gpr])
    (by rw [g₂.wr, g₁.wr]; exact hin 192 (by omega) (by omega)) fun s₃ g₃ => ?_
  refine wp_std hb (by decide) (by rw [g₃.gpr, g₂.gpr, g₁.gpr])
    (by rw [g₃.wr, g₂.wr, g₁.wr]; exact hin 200 (by omega) (by omega)) fun s₄ g₄ => ?_
  refine wp_std hb (by decide) (by rw [g₄.gpr, g₃.gpr, g₂.gpr, g₁.gpr])
    (by rw [g₄.wr, g₃.wr, g₂.wr, g₁.wr]; exact hin 208 (by omega) (by omega)) fun s₅ g₅ => ?_
  refine wp_std hb (by decide) (by rw [g₅.gpr, g₄.gpr, g₃.gpr, g₂.gpr, g₁.gpr])
    (by rw [g₅.wr, g₄.wr, g₃.wr, g₂.wr, g₁.wr]; exact hin 216 (by omega) (by omega)) fun s₆ g₆ => ?_
  refine k s₆ (by rw [g₆.gpr, g₅.gpr, g₄.gpr, g₃.gpr, g₂.gpr, g₁.gpr])
    (by rw [g₆.rd, g₅.rd, g₄.rd, g₃.rd, g₂.rd, g₁.rd]) (by rw [g₆.wr, g₅.wr, g₄.wr, g₃.wr, g₂.wr, g₁.wr])
    (by rw [g₆.sp, g₅.sp, g₄.sp, g₃.sp, g₂.sp, g₁.sp]) ?_
  rw [g₆.mem, g₅.mem, g₄.mem, g₃.mem, g₂.mem, g₁.mem]
  simp only [saveMem, g₅.gpr, g₄.gpr, g₃.gpr, g₂.gpr, g₁.gpr]

theorem frame_bytes {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {R : Region}
    (hd : ∀ r ∈ rs, R.Disjoint r) (hR : R.len ≤ 2 ^ 64) {i : Nat} (hi : i < R.len) :
    m' (R.base + BitVec.ofNat 64 i) = m (R.base + BitVec.ofNat 64 i) := by
  refine hf _ fun r hr hc => hd r hr _ ?_ hc
  simp only [Region.Contains]
  rw [show R.base + BitVec.ofNat 64 i - R.base = BitVec.ofNat 64 i by bv_omega,
    Proof.Sha512.PPC64LE.toNat_ofNat_lt (by omega)]
  omega

/-- Registers that no instruction writes keep their values, as a postcondition. -/
theorem WP.gprs {c : Prog isa} {s : State} {Q : State → Prop} (h : WP isa c s Q) {rs : List Reg}
    (hc : ∀ r ∈ rs, ∀ i ∈ instrs c, dstOf i ≠ some r)
    (hn : c.noCalls = true ∨ ∀ r ∈ rs, r ∉ linkRegs :=
      by first | exact .inr (by decide) | exact .inl (by decide +kernel)) :
    WP isa c s fun s' => Q s' ∧ ∀ r ∈ rs, s'.gpr r = s.gpr r := by
  obtain ⟨t, s', he, hq⟩ := h
  exact ⟨t, s', he, hq, fun r hr => Exec.gpr (hc r hr) he (hn.imp id fun h => h r hr)⟩

/-- The callee-saved registers no instruction writes, including those of
the compression function. -/
def untouched : List Reg := [.r2, .r20, .r21, .r22, .r23, .r24, .r25]

/-- The callee-saved registers only the compression function writes (it
saves and restores them). -/
def nvRegs : List Reg := [.r14, .r15, .r16, .r17, .r18, .r19]

theorem nv_pres : ∀ r ∈ nvRegs, r ∈ preserved := by decide

theorem restore_eq : restore = [.load .d .r26 .r27 176, .load .d .r28 .r27 192,
    .load .d .r29 .r27 200, .load .d .r30 .r27 208, .load .d .r31 .r27 216,
    .load .d .r27 .r27 184] := rfl

/-- Restoring `r26`–`r31` from the save area at `scr`. -/
theorem restore_ok {s : State} {scr : Addr} (h27 : s.gpr .r27 = scr)
    (hin : ∀ d, 176 ≤ d → d + 8 ≤ 224 → InRegions (s.rd ++ s.wr) (scr + BitVec.ofNat 64 d) 8)
    (g : Reg → BitVec 64) (hsv : ∀ p ∈ saved, s.mem.readW (scr + BitVec.ofNat 64 p.2) 64 = g p.1)
    {Q : State → Prop}
    (k : ∀ s', (∀ p ∈ saved, s'.gpr p.1 = g p.1) → (∀ r, r ∉ saved.map Prod.fst → s'.gpr r = s.gpr r) →
      s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp → Q s') :
    WP isa (.block restore) s Q := by
  have v : ∀ r d, (r, d) ∈ saved → s.mem.readW (scr + BitVec.ofNat 64 d) 64 = g r :=
    fun r d h => hsv (r, d) h
  rw [restore_eq]
  refine wp_ld (by decide) (by decide) (by rw [h27]) (hin 176 (by omega) (by omega)) fun s₁ u₁ => ?_
  refine wp_ld (by decide) (by decide) (by rw [u₁.other _ (by decide), h27])
    (by rw [u₁.rd, u₁.wr]; exact hin 192 (by omega) (by omega)) fun s₂ u₂ => ?_
  refine wp_ld (by decide) (by decide) (by rw [u₂.other _ (by decide), u₁.other _ (by decide), h27])
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact hin 200 (by omega) (by omega)) fun s₃ u₃ => ?_
  refine wp_ld (by decide) (by decide)
    (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h27])
    (by rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact hin 208 (by omega) (by omega))
    fun s₄ u₄ => ?_
  refine wp_ld (by decide) (by decide)
    (by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), h27])
    (by rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact hin 216 (by omega) (by omega))
    fun s₅ u₅ => ?_
  refine wp_ld (by decide) (by decide)
    (by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), h27])
    (by rw [u₅.rd, u₅.wr, u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]
        exact hin 184 (by omega) (by omega))
    fun s₆ u₆ => WP.block_nil ?_
  have m5 : s₅.mem = s.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  refine k s₆ (fun p hp => ?_) (fun r hr => ?_) (by rw [u₆.mem, m5]) (by rw [u₆.rd, u₅.rd, u₄.rd,
    u₃.rd, u₂.rd, u₁.rd]) (by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr])
    (by rw [u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp])
  · simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
        u₂.other _ (by decide), u₁.gpr, v .r26 176 (by simp [saved])]
    · rw [u₆.gpr, m5, v .r27 184 (by simp [saved])]
    · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
        u₂.gpr, u₁.mem, v .r28 192 (by simp [saved])]
    · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.mem, u₁.mem,
        v .r29 200 (by simp [saved])]
    · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.mem, u₂.mem, u₁.mem,
        v .r30 208 (by simp [saved])]
    · rw [u₆.other _ (by decide), u₅.gpr, u₄.mem, u₃.mem, u₂.mem, u₁.mem, v .r31 216 (by simp [saved])]
  · simp only [saved, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false,
      not_or] at hr
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hr
    rw [u₆.other _ h2, u₅.other _ h6, u₄.other _ h5, u₃.other _ h4, u₂.other _ h3, u₁.other _ h1]

/-- `x &&& 127`. -/
theorem and127 (x : BitVec 64) : x &&& BitVec.ofNat 64 127 = BitVec.ofNat 64 (x.toNat % 128) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (BitVec.ofNat 64 127).toNat = 2 ^ 7 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_ofNat]
  omega

/-! ## Byte order -/

theorem rev64_wordBytes (x : BitVec 64) :
    (List.range 8).map (fun j => (rev64 x).extractLsb' (8 * j) 8) = Spec.Sha512.wordBytes x := by
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
    List.cons_append, List.reverse_cons, List.reverse_nil, List.cons.injEq, and_true,
    Spec.Sha512.wordBytes]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [rev64, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]
    interval_cases i <;> simp

end VG.Proof.Sha512.PPC64LE.Stream
