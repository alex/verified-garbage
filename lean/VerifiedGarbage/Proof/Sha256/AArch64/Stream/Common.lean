import VerifiedGarbage.Proof.Sha256.AArch64.Compress
import VerifiedGarbage.Proof.Sha256.Stream
import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Impl.Sha256.AArch64.Stream

/-!
# Streaming SHA-256 on AArch64: common lemmas

Untrusted: everything here is checked by Lean. Weakest-precondition rules for
the instruction forms used, and the call of the compression function
(`compressAt`).
-/

namespace VG.Proof.Sha256.AArch64.Stream

open VG VG.AArch64 VG.Impl.Sha256.AArch64.Stream
open VG.Proof.Sha256.AArch64 (compress_verified)
open VG.Spec.Sha256 (HashValue stateAt blockAt compressBlocks compress parseBlock bytesAt)

/-! ## One instruction at a time -/

/-- `s'` is `s` with register `d` set to `v`. -/
structure Upd (s s' : State) (d : Reg) (v : BitVec 64) : Prop where
  gpr : s'.gpr d = v
  other : ∀ r, r ≠ d → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem Upd.write (s : State) (sz : Size) (d : Reg) (v : BitVec sz.bits) :
    Upd s (s.write sz d v) d (v.setWidth 64) :=
  ⟨by simp [State.write], fun r h => by simp [State.write, h], rfl, rfl, rfl, rfl⟩

theorem Upd.write64 (s : State) (d : Reg) (v : BitVec 64) : Upd s (s.write .x d v) d v := by
  simpa using Upd.write s .x d v

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

theorem wp_addImm {d n : Reg} {imm : Nat} (h : imm < 4096)
    (k : ∀ s', Upd s s' d (s.gpr n + BitVec.ofNat 64 imm) → WP isa (.block is) s' Q) :
    WP isa (.block (.addImm .x d n imm :: is)) s Q :=
  WP.cons (s' := s.write .x d (s.gpr n + BitVec.ofNat 64 imm)) (by simp [exec, h, State.read])
    (k _ (Upd.write64 _ _ _))

theorem wp_mov {d n : Reg} (k : ∀ s', Upd s s' d (s.gpr n) → WP isa (.block is) s' Q) :
    WP isa (.block (mov d n :: is)) s Q :=
  wp_addImm (by decide) fun s' u => k s' (by simpa using u)

theorem wp_subImm {d n : Reg} {imm : Nat} (h : imm < 4096)
    (k : ∀ s', Upd s s' d (s.gpr n - BitVec.ofNat 64 imm) → WP isa (.block is) s' Q) :
    WP isa (.block (.subImm .x d n imm :: is)) s Q :=
  WP.cons (s' := s.write .x d (s.gpr n - BitVec.ofNat 64 imm)) (by simp [exec, h, State.read])
    (k _ (Upd.write64 _ _ _))

theorem wp_movz {d : Reg} {imm : BitVec 16}
    (k : ∀ s', Upd s s' d (imm.setWidth 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.movz .x d imm 0 :: is)) s Q :=
  WP.cons (s' := s.write .x d (imm.setWidth 64)) (by simp [exec]) (k _ (Upd.write64 _ _ _))

theorem wp_add {d n m : Reg}
    (k : ∀ s', Upd s s' d (s.gpr n + s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.add .x d n m :: is)) s Q :=
  WP.cons (s' := s.write .x d (s.gpr n + s.gpr m)) (by simp [exec, State.read]) (k _ (Upd.write64 _ _ _))

theorem wp_sub {d n m : Reg}
    (k : ∀ s', Upd s s' d (s.gpr n - s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.sub .x d n m :: is)) s Q :=
  WP.cons (s' := s.write .x d (s.gpr n - s.gpr m)) (by simp [exec, State.read]) (k _ (Upd.write64 _ _ _))

theorem wp_and {d n m : Reg}
    (k : ∀ s', Upd s s' d (s.gpr n &&& s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.logic .and .x d n m :: is)) s Q :=
  WP.cons (s' := s.write .x d (s.gpr n &&& s.gpr m)) (by simp [exec, State.read])
    (k _ (Upd.write64 _ _ _))

theorem wp_lsr {d n : Reg} {sh : Nat} (h : sh < 64)
    (k : ∀ s', Upd s s' d (s.gpr n >>> sh) → WP isa (.block is) s' Q) :
    WP isa (.block (.lsr .x d n sh :: is)) s Q :=
  WP.cons (s' := s.write .x d (s.gpr n >>> sh)) (by simp [exec, h, State.read])
    (k _ (Upd.write64 _ _ _))

theorem wp_rev {d n : Reg}
    (k : ∀ s', Upd s s' d (rev64 (s.gpr n)) → WP isa (.block is) s' Q) :
    WP isa (.block (.rev d n :: is)) s Q :=
  WP.cons (s' := s.write .x d (rev64 (s.gpr n))) (by simp [exec, State.read]) (k _ (Upd.write64 _ _ _))

theorem wp_rev32 {d n : Reg}
    (k : ∀ s', Upd s s' d ((rev32 ((s.gpr n).setWidth 32)).setWidth 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.rev32 d n :: is)) s Q :=
  WP.cons rfl (k _ (Upd.write s .w d _))

theorem wp_ldrb {t n : Reg} {off : Nat} {a : Addr} (ho : off < 4096)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hin : InRegions (s.rd ++ s.wr) a 1)
    (k : ∀ s', Upd s s' t ((s.mem a).setWidth 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.ldrb t n off :: is)) s Q := by
  refine WP.cons (s' := s.write .w t (((s.mem a).setWidth 32))) ?_ (k _ ?_)
  · simp only [exec, addr, Nat.mod_one, true_and, show off < 4096 * 1 by omega, ite_true, ha,
      Option.bind_some, State.load, hin, Option.map_some, read_one]
  · have := Upd.write s .w t ((s.mem a).setWidth 32)
    have e : ((s.mem a).setWidth 32).setWidth 64 = (s.mem a).setWidth 64 := by
      ext i hi; simp
    rwa [e] at this

theorem wp_strb {t n : Reg} {off : Nat} {a : Addr} (ho : off < 4096)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hout : InRegions s.wr a 1)
    (k : ∀ s', Mupd s s' (s.mem.writeW a ((s.gpr t).setWidth 8)) → WP isa (.block is) s' Q) :
    WP isa (.block (.strb t n off :: is)) s Q := by
  refine WP.cons (s' := { s with mem := s.mem.writeW a ((s.gpr t).setWidth 8) }) ?_
    (k _ ⟨rfl, rfl, rfl, rfl, rfl⟩)
  simp only [exec, addr, Nat.mod_one, true_and, show off < 4096 * 1 by omega, ite_true, ha,
    Option.bind_some, State.store, hout, Mem.writeW, State.read]
  congr 3
  ext i hi; simp [Size.bits]; try omega

theorem wp_str {t n : Reg} {off : Nat} {a : Addr} (ho : off % 8 = 0 ∧ off < 4096 * 8)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hout : InRegions s.wr a 8)
    (k : ∀ s', Mupd s s' (s.mem.writeW a (s.gpr t)) → WP isa (.block is) s' Q) :
    WP isa (.block (.str .x t n off :: is)) s Q := by
  refine WP.cons (s' := { s with mem := s.mem.writeW a (s.gpr t) }) ?_ (k _ ⟨rfl, rfl, rfl, rfl, rfl⟩)
  simp only [exec, addr, Size.bytes, ho, and_self, ite_true, ha, Option.bind_some, State.store, hout,
    Mem.writeW, State.read]
  try rfl

theorem wp_str32 {t n : Reg} {off : Nat} {a : Addr} (ho : off % 4 = 0 ∧ off < 4096 * 4)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hout : InRegions s.wr a 4)
    (k : ∀ s', Mupd s s' (s.mem.writeW a ((s.gpr t).setWidth 32)) → WP isa (.block is) s' Q) :
    WP isa (.block (.str .w t n off :: is)) s Q := by
  refine WP.cons (s' := { s with mem := s.mem.writeW a ((s.gpr t).setWidth 32) }) ?_
    (k _ ⟨rfl, rfl, rfl, rfl, rfl⟩)
  simp only [exec, addr, Size.bytes, ho, and_self, ite_true, ha, Option.bind_some, State.store, hout,
    Mem.writeW, State.read]
  try rfl

theorem wp_ldr {t n : Reg} {off : Nat} {a : Addr} (ho : off % 8 = 0 ∧ off < 4096 * 8)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hin : InRegions (s.rd ++ s.wr) a 8)
    (k : ∀ s', Upd s s' t (s.mem.readW a 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.ldr .x t n off :: is)) s Q := by
  refine WP.cons (s' := s.write .x t (s.mem.readW a 64)) ?_ (k _ (Upd.write64 _ _ _))
  simp only [exec, addr, Size.bytes, ho, and_self, ite_true, ha, Option.bind_some, State.load, hin,
    Option.map_some, Mem.readW]
  try rfl

theorem wp_ldr32 {t n : Reg} {off : Nat} {a : Addr} (ho : off % 4 = 0 ∧ off < 4096 * 4)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hin : InRegions (s.rd ++ s.wr) a 4)
    (k : ∀ s', Upd s s' t ((s.mem.readW a 32).setWidth 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.ldr .w t n off :: is)) s Q := by
  refine WP.cons (s' := s.write .w t (s.mem.readW a 32)) ?_ (k _ (Upd.write s .w t _))
  simp only [exec, addr, Size.bytes, ho, and_self, ite_true, ha, Option.bind_some, State.load, hin,
    Option.map_some, Mem.readW]
  try rfl

end

/-! ## The inlined compression function -/

theorem compressBlocks_one (H : HashValue) (m : Mem) (p : Addr) :
    compressBlocks H m p 1 = compress H (blockAt m p) := by
  simp [compressBlocks]

theorem one_toNat : (BitVec.setWidth 64 (1 : BitVec 16)).toNat = 1 := rfl

theorem compress_noFrames : Impl.Sha256.AArch64.compress.noFrames = true := by decide +kernel

/-- Compressing the block at `x1` into the hash value at `x19`, with scratch
space at `x20`: the callee-saved registers other than `x30` are kept. -/
theorem compressAt_ok {s : State} {st scr src : Addr}
    (h19 : s.gpr .x19 = st) (h20 : s.gpr .x20 = scr) (h1 : s.gpr .x1 = src)
    (d₁ : Region.Disjoint ⟨st, 32⟩ ⟨scr, 112⟩) (d₂ : Region.Disjoint ⟨src, 64⟩ ⟨st, 32⟩)
    (d₃ : Region.Disjoint ⟨src, 64⟩ ⟨scr, 112⟩)
    (hc : Covers [⟨src, 64⟩, ⟨st, 32⟩, ⟨scr, 112⟩] (s.rd ++ s.wr))
    (hw : Covers [⟨st, 32⟩, ⟨scr, 112⟩] s.wr) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s.gpr r) →
      s'.sp = s.sp → Frame [⟨st, 32⟩, ⟨scr, 112⟩] s.mem s'.mem →
      stateAt s'.mem st = compress (stateAt s.mem st) (blockAt s.mem src) → Q s') :
    WP isa compressAt s Q := by
  unfold compressAt
  refine WP.seq (wp_mov fun s₁ u₁ => wp_movz fun s₂ u₂ => wp_mov fun s₃ u₃ => WP.block_nil ?_)
  have e0 : s₃.gpr .x0 = st := by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, h19]
  have e1 : s₃.gpr .x1 = src := by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h1]
  have e2 : s₃.gpr .x2 = BitVec.setWidth 64 (1 : BitVec 16) := by
    rw [u₃.other _ (by decide), u₂.gpr]
  have e3 : s₃.gpr .x3 = scr := by
    rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), h20]
  have keep : ∀ r ∈ preserved, s₃.gpr r = s.gpr r := by
    intro r hr
    have : r ≠ .x0 ∧ r ≠ .x2 ∧ r ≠ .x3 := by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        decide
    rw [u₃.other _ this.2.2, u₂.other _ this.2.1, u₁.other _ this.1]
  have m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  have rd₃ : s₃.rd = s.rd := by rw [u₃.rd, u₂.rd, u₁.rd]
  have wr₃ : s₃.wr = s.wr := by rw [u₃.wr, u₂.wr, u₁.wr]
  have sp₃ : s₃.sp = s.sp := by rw [u₃.sp, u₂.sp, u₁.sp]
  have c0 : s₃.callEntry.gpr .x0 = st := (State.callEntry_gpr _ (by decide)).trans e0
  have c1 : s₃.callEntry.gpr .x1 = src := (State.callEntry_gpr _ (by decide)).trans e1
  have c2 : s₃.callEntry.gpr .x2 = BitVec.setWidth 64 (1 : BitVec 16) :=
    (State.callEntry_gpr _ (by decide)).trans e2
  have c3 : s₃.callEntry.gpr .x3 = scr := (State.callEntry_gpr _ (by decide)).trans e3
  refine WP.call (k := Proof.Sha256.compressAArch64) compress_verified.1
    (rd := [⟨src, 64 * 1⟩]) (wr := [⟨st, 32⟩, ⟨scr, 112⟩]) ?_ ?_ ?_ ?_ compress_noFrames
  · simp only [Proof.Sha256.compressAArch64, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, c0, c1, c2, c3, one_toNat]
    exact ⟨trivial, trivial, d₁, d₂, d₃⟩
  · rw [rd₃, wr₃]; simpa using hc
  · rw [wr₃]; exact hw
  · intro s' hrd hwr hsp hf hcs _ hpost
    simp only [Proof.Sha256.compressAArch64, State.withRegions_gpr, State.withRegions_mem,
      State.callEntry_mem, c0, c1, c2, one_toNat, compressBlocks_one, m₃] at hpost
    exact hQ s' (hrd.trans rd₃) (hwr.trans wr₃) (fun r hr h30 => (hcs r hr h30).trans (keep r hr))
      (hsp.trans sp₃) (m₃ ▸ hf) hpost

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

/-- `x >>> 6`, of a number below 2⁶⁴. -/
theorem ofNat_shr6 {a : Nat} (h : a < 2 ^ 64) : BitVec.ofNat 64 a >>> 6 = BitVec.ofNat 64 (a / 64) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h,
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (by omega)]

theorem bytesAt_getD {m : Mem} {p : Addr} {n : Nat} {l : List Byte} (h : bytesAt m p n = l) {k : Nat}
    (hk : k < n) : m (p + BitVec.ofNat 64 k) = l.getD k 0 := by
  subst h; simp [bytesAt, List.getD_eq_getElem?_getD, hk]

/-- `eval` of the branch conditions. -/
theorem eval_zero (s : State) (r : Reg) : eval (.zero .x r) s = some (s.gpr r == 0) := by
  simp [eval, State.read]

theorem eval_nonzero (s : State) (r : Reg) : eval (.nonzero .x r) s = some (s.gpr r != 0) := by
  simp [eval, State.read]

/-! ## Saving the caller's registers -/

/-- The memory after saving `x19`–`x24` (values `g`) at `b + 112 … b + 152`. -/
def saveMem (m : Mem) (b : Addr) (g : Reg → BitVec 64) : Mem :=
  (((((m.writeW (b + BitVec.ofNat 64 112) (g .x19)).writeW (b + BitVec.ofNat 64 120) (g .x20)).writeW
    (b + BitVec.ofNat 64 128) (g .x21)).writeW (b + BitVec.ofNat 64 136) (g .x22)).writeW
    (b + BitVec.ofNat 64 144) (g .x23)).writeW (b + BitVec.ofNat 64 152) (g .x24)

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
    Frame [⟨b, 160⟩] m (saveMem m b g) := by
  have c : ∀ d : Nat, d + 8 ≤ 160 → (⟨b, 160⟩ : Region).Contains (b + BitVec.ofNat 64 d) (64 / 8) :=
    fun d hd => Proof.Sha256.AArch64.contains_offset hd (by omega)
  simp only [saveMem]
  exact (((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 112 (by omega))).writeW
    (List.mem_singleton_self _) _ (c 120 (by omega))).writeW (List.mem_singleton_self _) _
    (c 128 (by omega))).writeW (List.mem_singleton_self _) _ (c 136 (by omega))).writeW
    (List.mem_singleton_self _) _ (c 144 (by omega)) |>.writeW (List.mem_singleton_self _) _
    (c 152 (by omega))

theorem save_eq (b : Reg) : save b = [.str .x .x19 b 112, .str .x .x20 b 120, .str .x .x21 b 128,
    .str .x .x22 b 136, .str .x .x23 b 144, .str .x .x24 b 152] := rfl

/-- Saving `x19`–`x24` with the scratch pointer in `b`. -/
theorem save_ok {b : Reg} {rest : List Instr} {s : State} {Q : State → Prop}
    (hin : ∀ d, 112 ≤ d → d + 8 ≤ 160 → InRegions s.wr (s.gpr b + BitVec.ofNat 64 d) 8)
    (k : ∀ s', s'.gpr = s.gpr → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      s'.mem = saveMem s.mem (s.gpr b) s.gpr → WP isa (.block rest) s' Q) :
    WP isa (.block (save b ++ rest)) s Q := by
  rw [save_eq]
  simp only [List.cons_append, List.nil_append]
  refine wp_str (by decide) rfl (hin 112 (by omega) (by omega)) fun s₁ g₁ => ?_
  refine wp_str (by decide) (by rw [g₁.gpr]) (by rw [g₁.wr]; exact hin 120 (by omega) (by omega))
    fun s₂ g₂ => ?_
  refine wp_str (by decide) (by rw [g₂.gpr, g₁.gpr])
    (by rw [g₂.wr, g₁.wr]; exact hin 128 (by omega) (by omega)) fun s₃ g₃ => ?_
  refine wp_str (by decide) (by rw [g₃.gpr, g₂.gpr, g₁.gpr])
    (by rw [g₃.wr, g₂.wr, g₁.wr]; exact hin 136 (by omega) (by omega)) fun s₄ g₄ => ?_
  refine wp_str (by decide) (by rw [g₄.gpr, g₃.gpr, g₂.gpr, g₁.gpr])
    (by rw [g₄.wr, g₃.wr, g₂.wr, g₁.wr]; exact hin 144 (by omega) (by omega)) fun s₅ g₅ => ?_
  refine wp_str (by decide) (by rw [g₅.gpr, g₄.gpr, g₃.gpr, g₂.gpr, g₁.gpr])
    (by rw [g₅.wr, g₄.wr, g₃.wr, g₂.wr, g₁.wr]; exact hin 152 (by omega) (by omega)) fun s₆ g₆ => ?_
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
    Proof.Sha256.AArch64.toNat_ofNat_lt (by omega)]
  omega

/-- Registers that no instruction writes keep their values, as a postcondition. -/
theorem WP.gprs {c : Prog isa} {s : State} {Q : State → Prop} (h : WP isa c s Q) {rs : List Reg}
    (hc : ∀ r ∈ rs, ∀ i ∈ instrs c, dstOf i ≠ some r)
    (hn : c.noCalls = true ∨ ∀ r ∈ rs, r ∉ linkRegs :=
      by first | exact .inr (by decide) | exact .inl (by decide +kernel)) :
    WP isa c s fun s' => Q s' ∧ ∀ r ∈ rs, s'.gpr r = s.gpr r := by
  obtain ⟨t, s', he, hq⟩ := h
  exact ⟨t, s', he, hq, fun r hr => Exec.gpr (hc r hr) he (hn.imp id fun h => h r hr)⟩

/-- The callee-saved registers our code never touches (but for `x30`, which
our calls change and the frame restores). -/
def untouched : List Reg := [.x25, .x26, .x27, .x28, .x29]

/-- A byte of a region disjoint from a frame is unchanged by the push. -/
theorem write_frame_apply {m : Mem} {sp : Addr} {v : BitVec (8 * 8)} {R : Region}
    (hd : Region.Disjoint ⟨sp - 16, 16⟩ R) {x : Addr} (hx : R.Contains x 1) :
    m.write (sp - 16) 8 v x = m x :=
  Mem.write_apply fun h => hd x (by simp only [Region.Contains]; omega) hx

/-- The bytes of a region disjoint from a frame are unchanged by the push. -/
theorem write_frame_bytes {m : Mem} {sp : Addr} {v : BitVec (8 * 8)} {R : Region}
    (hd : Region.Disjoint ⟨sp - 16, 16⟩ R) (hR : R.len < 2 ^ 64) {i : Nat} (hi : i < R.len) :
    m.write (sp - 16) 8 v (R.base + BitVec.ofNat 64 i) = m (R.base + BitVec.ofNat 64 i) :=
  write_frame_apply hd (by
    simp only [Region.Contains]
    rw [show R.base + BitVec.ofNat 64 i - R.base = BitVec.ofNat 64 i by bv_omega,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    omega)

theorem restore_eq : restore = [.ldr .x .x19 .x20 112, .ldr .x .x21 .x20 128, .ldr .x .x22 .x20 136,
    .ldr .x .x23 .x20 144, .ldr .x .x24 .x20 152, .ldr .x .x20 .x20 120] := rfl

/-- Restoring `x19`–`x24` from the save area at `scr`. -/
theorem restore_ok {s : State} {scr : Addr} (h20 : s.gpr .x20 = scr)
    (hin : ∀ d, 112 ≤ d → d + 8 ≤ 160 → InRegions (s.rd ++ s.wr) (scr + BitVec.ofNat 64 d) 8)
    (g : Reg → BitVec 64) (hsv : ∀ p ∈ saved, s.mem.readW (scr + BitVec.ofNat 64 p.2) 64 = g p.1)
    {Q : State → Prop}
    (k : ∀ s', (∀ p ∈ saved, s'.gpr p.1 = g p.1) → (∀ r, r ∉ saved.map Prod.fst → s'.gpr r = s.gpr r) →
      s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp → Q s') :
    WP isa (.block restore) s Q := by
  have v : ∀ r d, (r, d) ∈ saved → s.mem.readW (scr + BitVec.ofNat 64 d) 64 = g r :=
    fun r d h => hsv (r, d) h
  rw [restore_eq]
  refine wp_ldr (by decide) (by rw [h20]) (hin 112 (by omega) (by omega)) fun s₁ u₁ => ?_
  refine wp_ldr (by decide) (by rw [u₁.other _ (by decide), h20])
    (by rw [u₁.rd, u₁.wr]; exact hin 128 (by omega) (by omega)) fun s₂ u₂ => ?_
  refine wp_ldr (by decide) (by rw [u₂.other _ (by decide), u₁.other _ (by decide), h20])
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact hin 136 (by omega) (by omega)) fun s₃ u₃ => ?_
  refine wp_ldr (by decide)
    (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h20])
    (by rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact hin 144 (by omega) (by omega))
    fun s₄ u₄ => ?_
  refine wp_ldr (by decide)
    (by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), h20])
    (by rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact hin 152 (by omega) (by omega))
    fun s₅ u₅ => ?_
  refine wp_ldr (by decide)
    (by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), h20])
    (by rw [u₅.rd, u₅.wr, u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]
        exact hin 120 (by omega) (by omega))
    fun s₆ u₆ => WP.block_nil ?_
  have m5 : s₅.mem = s.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  refine k s₆ (fun p hp => ?_) (fun r hr => ?_) (by rw [u₆.mem, m5]) (by rw [u₆.rd, u₅.rd, u₄.rd,
    u₃.rd, u₂.rd, u₁.rd]) (by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr])
    (by rw [u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp])
  · simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
        u₂.other _ (by decide), u₁.gpr, v .x19 112 (by simp [saved])]
    · rw [u₆.gpr, m5, v .x20 120 (by simp [saved])]
    · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
        u₂.gpr, u₁.mem, v .x21 128 (by simp [saved])]
    · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.mem, u₁.mem,
        v .x22 136 (by simp [saved])]
    · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.mem, u₂.mem, u₁.mem,
        v .x23 144 (by simp [saved])]
    · rw [u₆.other _ (by decide), u₅.gpr, u₄.mem, u₃.mem, u₂.mem, u₁.mem, v .x24 152 (by simp [saved])]
  · simp only [saved, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false,
      not_or] at hr
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hr
    rw [u₆.other _ h2, u₅.other _ h6, u₄.other _ h5, u₃.other _ h4, u₂.other _ h3, u₁.other _ h1]

/-- `x &&& 63`. -/
theorem and63 (x : BitVec 64) : x &&& (BitVec.setWidth 64 (63 : BitVec 16)) = BitVec.ofNat 64 (x.toNat % 64) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, show (BitVec.setWidth 64 (63 : BitVec 16)).toNat = 2 ^ 6 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]
  omega

end VG.Proof.Sha256.AArch64.Stream
