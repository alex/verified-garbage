import VerifiedGarbage.Proof.Blake2.X86.Contract
import VerifiedGarbage.Proof.MdStream.X86.Common
import VerifiedGarbage.Proof.Framework.X86.Wp
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Impl.Blake2.X86.Stream

/-!
# Streaming BLAKE2 on x86 (32-bit): common lemmas

Untrusted: everything here is checked by Lean. What the proofs of `init`,
`update` and `finalize` need of the parameters (`Ok`) and of the compression
function they call (`CalleeOk`: BLAKE2s's or BLAKE2b's, verified against
`compressX86`), the call (`call_ok`), and the loop copying bytes into the
buffer (`copyLoop_ok`).
-/

namespace VG.Proof.Blake2.X86.Stream

open VG VG.X86 VG.X86.Wp VG.Spec.Blake2
open VG.Impl.Blake2.X86 (at_)
open VG.Impl.Blake2.X86.Stream
open VG.Proof.Blake2 (compressX86 stateAt_congr compressBlocks_congr)
open VG.WriteBytes (writeBytes writeBytes_snoc writeBytes_frame writeBytes_nil)

variable {w : Nat} {P : Params w}

/-- The word sizes. -/
structure Ok (P : Params w) : Prop where
  /-- A key fits in a block. -/
  max : P.maxBytes ≤ blockBytes w
  w : w = 64 ∨ w = 32

theorem Ok.bb (h : Ok P) : blockBytes w = 64 ∨ blockBytes w = 128 := by
  rcases h.w with rfl | rfl <;> decide

theorem Ok.N (h : Ok P) : bufOff w = blockBytes w / 2 := by
  rcases h.w with rfl | rfl <;> decide

theorem Ok.pos (h : Ok P) : 0 < blockBytes w := by rcases h.bb with h | h <;> omega

theorem Ok.len (h : Ok P) : bufOff w + blockBytes w ≤ 192 := by
  rcases h.w with rfl | rfl <;> decide

theorem N_eq : Impl.Blake2.X86.Stream.N w = bufOff w := rfl
theorem B_eq : Impl.Blake2.X86.Stream.B w = blockBytes w := rfl

/-- What the calls need of the compression function: its contract, and that
it does not touch `esp` but to call, and calls nothing that uses the stack. -/
structure CalleeOk (P : Params w) (code : Prog isa) : Prop where
  verified : ∀ s, (compressX86 P).pre s →
    ∃ t s', Exec isa code s t s' ∧ abiPreserved s s' ∧ (compressX86 P).post s s'
  nosp : NoSp code
  stack : stackUse code = 0

/-- `CalleeOk` from the compression function's `Verified` proof and two
checks the kernel evaluates (`NoSp.of_all (by lit_decide)`, `by lit_decide`). -/
theorem CalleeOk.of_verified {code : Prog isa} (hv : Verified X86.target code (compressX86 P))
    (hn : NoSp code) (hs : stackUse code = 0) : CalleeOk P code :=
  ⟨hv.1, hn, hs⟩


/-! ## Instructions that keep the flags -/

section
variable {is : List Instr} {s : State} {Q : State → Prop}

/-- `mov d, [b + o]`, which keeps the flags. -/
theorem wp_ldmF {d b : Reg} {B : BitVec 32} {o : Nat} (hb : s.gpr b = B)
    (hin : InRegions (s.rd ++ s.wr) (addr B o) 4)
    (k : ∀ s', Upd s s' d (s.mem.readW (addr B o) 32) → s'.cf = s.cf → s'.zf = s.zf →
      WP isa (.block is) s' Q) :
    WP isa (.block (.mov d (.mem ⟨b, o⟩) :: is)) s Q :=
  cons (s' := s.setReg d _) (by simp [exec, readSrc_mem hb hin]) (k _ (Upd.setReg _ _ _) rfl rfl)

/-- `mov d, r`, which keeps the flags. -/
theorem wp_movF {d r : Reg}
    (k : ∀ s', Upd s s' d (s.gpr r) → s'.cf = s.cf → s'.zf = s.zf → WP isa (.block is) s' Q) :
    WP isa (.block (.mov d (.reg r) :: is)) s Q :=
  cons rfl (k _ (Upd.setReg _ _ _) rfl rfl)

/-- `mov d, v`, which keeps the flags. -/
theorem wp_moviF {d : Reg} {v : BitVec 32}
    (k : ∀ s', Upd s s' d v → s'.cf = s.cf → s'.zf = s.zf → WP isa (.block is) s' Q) :
    WP isa (.block (.mov d (.imm v) :: is)) s Q :=
  cons rfl (k _ (Upd.setReg _ _ _) rfl rfl)

/-- `add d, v`, and the carry. -/
theorem wp_addiC {d : Reg} {v : BitVec 32}
    (k : ∀ s', Upd s s' d (s.gpr d + v) → s'.cf = some (decide (2 ^ 32 ≤ (s.gpr d).toNat + v.toNat)) →
      WP isa (.block is) s' Q) :
    WP isa (.block (.alu .add d (.imm v) :: is)) s Q :=
  cons rfl (k _ (Upd.flags _ _ _ _ _ _) rfl)

/-- `adc d, 0`, after a carry `c`. -/
theorem wp_adc0 {d : Reg} {c : Bool} (hc : s.cf = some c)
    (k : ∀ s', Upd s s' d (s.gpr d + (BitVec.ofBool c).setWidth 32) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .adc d (.imm 0) :: is)) s Q := by
  have hx : exec (.alu .adc d (.imm 0)) s = some ((arithFlags s (s.gpr d + 0 + (BitVec.ofBool c).setWidth 32)
      (decide (2 ^ 32 ≤ (s.gpr d).toNat + (0 : BitVec 32).toNat + c.toNat))
      (addOverflow (s.gpr d) 0 (s.gpr d + 0 + (BitVec.ofBool c).setWidth 32))).setReg d
      (s.gpr d + 0 + (BitVec.ofBool c).setWidth 32)) := by
    simp only [exec, execAlu, readSrc, Option.bind_some, hc, Option.map_some]
  refine cons hx (k _ ⟨?_, fun r h => ?_, rfl, rfl, rfl⟩)
  · simp [State.setReg]
  · simp [State.setReg, arithFlags, State.setFlags, h]

/-- `and d, v`, and ZF. -/
theorem wp_andiZ {d : Reg} {v : BitVec 32}
    (k : ∀ s', Upd s s' d (s.gpr d &&& v) → s'.zf = some (s.gpr d &&& v == 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .and d (.imm v) :: is)) s Q :=
  cons rfl (k _ (Upd.flags _ _ _ _ _ _) rfl)

/-- `or d, r`, and ZF. -/
theorem wp_orZ {d r : Reg}
    (k : ∀ s', Upd s s' d (s.gpr d ||| s.gpr r) → s'.zf = some (s.gpr d ||| s.gpr r == 0) →
      WP isa (.block is) s' Q) :
    WP isa (.block (.alu .or d (.reg r) :: is)) s Q :=
  cons rfl (k _ (Upd.flags _ _ _ _ _ _) rfl)

end

/-! ## 64-bit counters as two words -/

theorem lo_ofNat (T : Nat) : (BitVec.ofNat 32 T).toNat = T % 2 ^ 32 := BitVec.toNat_ofNat _ _

/-- The carry of adding `a < 2^32` to the low word of `T`, added to its high
word: the high word of `T + a`. -/
theorem carry_ofNat (T a : Nat) (ha : a < 2 ^ 32) :
    BitVec.ofNat 32 (T / 2 ^ 32) +
        (BitVec.ofBool (decide (2 ^ 32 ≤ (BitVec.ofNat 32 T).toNat + (BitVec.ofNat 32 a).toNat))).setWidth 32 =
      BitVec.ofNat 32 ((T + a) / 2 ^ 32) := by
  apply BitVec.eq_of_toNat_eq
  rw [lo_ofNat, lo_ofNat, Nat.mod_eq_of_lt ha]
  by_cases h : 2 ^ 32 ≤ T % 2 ^ 32 + a
  · simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_setWidth, BitVec.toNat_ofBool, h,
      decide_true, Bool.toNat_true]
    omega
  · simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_setWidth, BitVec.toNat_ofBool, h,
      decide_false, Bool.toNat_false]
    omega

/-- The two words of `T < 2^64`, high word first, are `T`. -/
theorem append_ofNat {T : Nat} (h : T < 2 ^ 64) :
    (BitVec.ofNat 32 (T / 2 ^ 32) ++ BitVec.ofNat 32 T).toNat = T := by
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt (BitVec.ofNat 32 T).isLt, Nat.shiftLeft_eq,
    lo_ofNat, lo_ofNat, Nat.mod_eq_of_lt (by omega)]
  omega

theorem append_toNat_mod (a b : BitVec 32) : (a ++ b).toNat % 2 ^ 32 = b.toNat := by
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt b.isLt, Nat.shiftLeft_eq]
  have := b.isLt; omega

theorem append_toNat_div (a b : BitVec 32) : (a ++ b).toNat / 2 ^ 32 = a.toNat := by
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt b.isLt, Nat.shiftLeft_eq]
  have := b.isLt; omega

theorem lo_append (a b : BitVec 32) : BitVec.ofNat 32 (a ++ b).toNat = b := by
  apply BitVec.eq_of_toNat_eq; rw [lo_ofNat, append_toNat_mod]

theorem hi_append (a b : BitVec 32) : BitVec.ofNat 32 ((a ++ b).toNat / 2 ^ 32) = a := by
  apply BitVec.eq_of_toNat_eq; rw [lo_ofNat, append_toNat_div, Nat.mod_eq_of_lt a.isLt]



/-! ## Addresses and bytes -/

/-- `x + c`, zero-extended, where it does not wrap around. -/
theorem sw_add {x : BitVec 32} {c : Nat} (h : x.toNat + c < 2 ^ 32) :
    (x + BitVec.ofNat 32 c).setWidth 64 = x.setWidth 64 + BitVec.ofNat 64 c := by
  have := MdStream.X86.addr_add_ofNat (x := x) (k := c) (d := 0) (by omega)
  simpa [addr] using this

theorem toNat_add_ofNat {x : BitVec 32} {c : Nat} (h : x.toNat + c < 2 ^ 32) :
    (x + BitVec.ofNat 32 c).toNat = x.toNat + c := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := c) (by omega), Nat.mod_eq_of_lt h]

theorem bytesAt_length (m : Mem) (p : Addr) (n : Nat) : (bytesAt m p n).length = n := by simp [bytesAt]

/-- Bytes `[0, r)` from `p` stay, and the bytes `xs` follow them. -/
theorem bytesAt_writeBytes (m : Mem) (p : Addr) (r : Nat) (xs : List Byte) (h : r + xs.length < 2 ^ 64) :
    bytesAt (writeBytes m (p + BitVec.ofNat 64 r) xs) p (r + xs.length) = bytesAt m p r ++ xs := by
  simp only [bytesAt, List.range_add, List.map_append, List.map_map]
  congr 1
  · apply List.map_congr_left
    intro i hi
    have hi := List.mem_range.mp hi
    exact VG.WriteBytes.writeBytes_before m p xs hi (by omega)
  · apply List.ext_getElem (by simp)
    intro j h₁ h₂
    simp only [List.getElem_map, List.getElem_range, Function.comp, writeBytes]
    have hj : j < xs.length := by simpa using h₁
    rw [show p + BitVec.ofNat 64 (r + j) - (p + BitVec.ofNat 64 r) = BitVec.ofNat 64 j from
      Offset.add_ofNat_add_sub p r j, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    simp [hj, List.getD_eq_getElem?_getD]

/-! ## The streaming state depends only on its bytes -/

theorem reprR_congr (hP : Ok P) {h0 : HashValue w} {mem mem' : Mem} {p : Addr} {d : List Byte} {r : Nat}
    (hm : ∀ i < bufOff w + blockBytes w, mem' (p + BitVec.ofNat 64 i) = mem (p + BitVec.ofNat 64 i))
    (h : Proof.Blake2.ReprR P h0 mem p d r) : Proof.Blake2.ReprR P h0 mem' p d r := by
  have hN := hP.len
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨h1, h2, h3, by rw [← h4]; exact stateAt_congr fun i hi => hm i (by omega), ?_⟩
  rw [← h5]
  refine Proof.Blake2.bytesAt_congr fun i hi => ?_
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  exact hm _ (by omega)

theorem repr_congr (hP : Ok P) {h0 : HashValue w} {mem mem' : Mem} {p : Addr} {d : List Byte}
    (hm : ∀ i < bufOff w + blockBytes w, mem' (p + BitVec.ofNat 64 i) = mem (p + BitVec.ofNat 64 i))
    (h : Spec.Blake2.Repr P h0 mem p d) : Spec.Blake2.Repr P h0 mem' p d := by
  rw [Proof.Blake2.repr_iff P hP.pos] at h ⊢
  exact reprR_congr hP hm h

/-- The 32 bytes of stack below `E`, as the contracts write them. -/
theorem stk_eq {E : BitVec 32} (h : 32 ≤ E.toNat) : below E 32 = ⟨E.setWidth 64 - 32, 32⟩ := by
  simp only [below]; rw [Taint.sub_setWidth h]; rfl

/-! ## The number of bytes in the buffer -/

theorem or_beq_zero (a b : BitVec 32) : (a ||| b == 0) = decide ((a ++ b).toNat = 0) := by
  have h1 := append_toNat_mod a b
  have h2 := append_toNat_div a b
  by_cases h : (a ++ b).toNat = 0
  · have ha : a = 0 := BitVec.eq_of_toNat_eq (by rw [← h2, h]; rfl)
    have hb : b = 0 := BitVec.eq_of_toNat_eq (by rw [← h1, h]; rfl)
    simp [ha, hb]
  · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro hab
    obtain ⟨ha, hb⟩ := BitVec.or_eq_zero_iff.mp hab
    apply h
    rw [ha, hb]; rfl

theorem and_mask (hP : Ok P) (x : BitVec 32) :
    x &&& BitVec.ofNat 32 (B w - 1) = BitVec.ofNat 32 (x.toNat % blockBytes w) := by
  rw [B_eq]
  apply BitVec.eq_of_toNat_eq
  rcases hP.bb with h | h <;> rw [h] <;> simp only [BitVec.toNat_and, BitVec.toNat_ofNat]
  · rw [show (64 - 1) % 2 ^ 32 = 2 ^ 6 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]; omega
  · rw [show (128 - 1) % 2 ^ 32 = 2 ^ 7 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]; omega

theorem mask_ofNat (hP : Ok P) {T : Nat} (hT : T ≠ 0) :
    ((BitVec.ofNat 32 T - 1) &&& BitVec.ofNat 32 (B w - 1)) + 1 =
      BitVec.ofNat 32 ((T - 1) % blockBytes w + 1) := by
  rw [and_mask hP]
  apply BitVec.eq_of_toNat_eq
  have := hP.bb
  have h1 : (1 : BitVec 32).toNat = 1 := rfl
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, h1]
  rcases this with h | h <;> rw [h] <;> omega

/-! ## Our caller's registers, saved in `scratch[512..528)` -/

/-- Our caller's registers are saved in the scratch space at `scr`. -/
def Saved (scr : BitVec 32) (s₀ : State) (m : Mem) : Prop :=
  ∀ p ∈ saved, m.readW (addr scr p.2) 32 = s₀.gpr p.1

/-- The memory after saving them. -/
def saveMem (scr : BitVec 32) (s₀ : State) : Mem :=
  (((s₀.mem.writeW (addr scr 512) (s₀.gpr .ebx)).writeW (addr scr 516) (s₀.gpr .esi)).writeW
    (addr scr 520) (s₀.gpr .edi)).writeW (addr scr 524) (s₀.gpr .ebp)

section
variable {scr : BitVec 32} (hfit : scr.toNat + 576 ≤ 2 ^ 32)
include hfit

theorem scr_contains {d n : Nat} (hd : d + n ≤ 576) (hn : 0 < n) :
    (⟨scr.setWidth 64, 576⟩ : Region).Contains (addr scr d) n :=
  MdStream.X86.contains_addr hd hn hfit

theorem rw_scr (m : Mem) (v : BitVec 32) {d e : Nat} (hd : d + 4 ≤ 576) (he : e + 4 ≤ 576)
    (h : d + 4 ≤ e ∨ e + 4 ≤ d) :
    (m.writeW (addr scr e) v).readW (addr scr d) 32 = m.readW (addr scr d) 32 :=
  MdStream.X86.readW_writeW_addr m v (by omega) (by omega) h

theorem saveMem_frame (s₀ : State) : Frame [⟨scr.setWidth 64, 576⟩] s₀.mem (saveMem scr s₀) := by
  have c : ∀ d, d + 4 ≤ 576 → (⟨scr.setWidth 64, 576⟩ : Region).Contains (addr scr d) (32 / 8) :=
    fun d hd => scr_contains hfit hd (by omega)
  simp only [saveMem]
  exact ((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 512 (by omega))).writeW
    (List.mem_singleton_self _) _ (c 516 (by omega))).writeW (List.mem_singleton_self _) _
    (c 520 (by omega))).writeW (List.mem_singleton_self _) _ (c 524 (by omega))

theorem saveMem_saved (s₀ : State) : Saved scr s₀ (saveMem scr s₀) := by
  have w := rw_scr hfit
  intro p hp'
  simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp'
  rcases hp' with rfl | rfl | rfl | rfl <;> simp only [saveMem]
  · rw [w _ _ (d := 512) (e := 524) (by omega) (by omega) (by omega),
      w _ _ (d := 512) (e := 520) (by omega) (by omega) (by omega),
      w _ _ (d := 512) (e := 516) (by omega) (by omega) (by omega), Mem.readW_writeW_self32]
  · rw [w _ _ (d := 516) (e := 524) (by omega) (by omega) (by omega),
      w _ _ (d := 516) (e := 520) (by omega) (by omega) (by omega), Mem.readW_writeW_self32]
  · rw [w _ _ (d := 520) (e := 524) (by omega) (by omega) (by omega), Mem.readW_writeW_self32]
  · rw [Mem.readW_writeW_self32]

/-- A word of the scratch space from offset `d ≥ 512` on is kept by writes
elsewhere: to regions disjoint from the scratch space, or to its first 512
bytes. -/
theorem keep_hi {rs : List Region} {m m' : Mem} (hf : Frame (⟨scr.setWidth 64, 512⟩ :: rs) m m')
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨scr.setWidth 64, 576⟩ r) {d : Nat} (h₁ : 512 ≤ d) (h₂ : d + 4 ≤ 576) :
    m'.readW (addr scr d) 32 = m.readW (addr scr d) 32 := by
  refine hf.readW (r := ⟨addr scr d, 4⟩) (Region.contains_self _ _) ?_ (by decide)
  intro r hr
  simp only [List.mem_cons] at hr
  rcases hr with rfl | hr
  · rw [addr_eq (by omega)]; exact Offset.disjoint_base _ h₁ (by omega)
  · refine (hd r hr).sub_left ?_
    rw [addr_eq (by omega)]; exact MdStream.X86.sub_offset h₂ (by omega)

theorem Saved.keep {s₀ : State} {rs : List Region} {m m' : Mem} (h : Saved scr s₀ m)
    (hf : Frame (⟨scr.setWidth 64, 512⟩ :: rs) m m')
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨scr.setWidth 64, 576⟩ r) : Saved scr s₀ m' := by
  intro p hp
  have : 512 ≤ p.2 ∧ p.2 + 4 ≤ 528 := by
    simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> decide
  rw [keep_hi hfit hf hd this.1 (by omega)]; exact h p hp

end

/-! ## The call -/

theorem frame_ne : [Reg.ebp, .eax, .edx, .ecx, .edi, .esi, .ebx] ≠ [] := by simp

theorem frame_esp : Reg.esp ∉ [Reg.ebp, .eax, .edx, .ecx, .edi, .esi, .ebx] := by decide

/-- Compressing the `k` blocks at `esi` (`blk`) into the state at `ebx`
(`st`), with the scratch space at `ebp` (`scr`), the counter in `edx:ecx` and
the final block flag in `eax`: a call of `compress(st, blk, k, t, last, scr)`
in a frame of its arguments, which uses the 32 bytes below `esp` (`E`) and
writes only there, the hash value and the first 512 bytes of the scratch
space. -/
theorem call_ok {name : String} {code : Prog isa} (hf : CalleeOk P code) {s : State}
    {st scr blk E tlo thi lst : BitVec 32} {k : Nat}
    (hesp : s.gpr .esp = E) (hS : s.gpr .ebx = st) (hC : s.gpr .ebp = scr) (hB : s.gpr .esi = blk)
    (hk : (s.gpr .edi).toNat = k) (hlo : s.gpr .ecx = tlo) (hhi : s.gpr .edx = thi)
    (hl : s.gpr .eax = lst)
    (hE : 32 ≤ E.toNat) (f₀ : st.toNat + bufOff w ≤ 2 ^ 32) (f₁ : blk.toNat + blockBytes w * k ≤ 2 ^ 32)
    (f₃ : scr.toNat + 512 ≤ 2 ^ 32)
    (d₁ : Region.Disjoint ⟨st.setWidth 64, bufOff w⟩ ⟨scr.setWidth 64, 512⟩)
    (d₂ : Region.Disjoint ⟨blk.setWidth 64, blockBytes w * k⟩ ⟨st.setWidth 64, bufOff w⟩)
    (d₃ : Region.Disjoint ⟨blk.setWidth 64, blockBytes w * k⟩ ⟨scr.setWidth 64, 512⟩)
    (dS : Region.Disjoint (below E 32) ⟨st.setWidth 64, bufOff w⟩)
    (dC : Region.Disjoint (below E 32) ⟨scr.setWidth 64, 512⟩)
    (dB : Region.Disjoint (below E 32) ⟨blk.setWidth 64, blockBytes w * k⟩)
    (hc : Covers [⟨blk.setWidth 64, blockBytes w * k⟩] (s.rd ++ s.wr))
    (hw : Covers [⟨st.setWidth 64, bufOff w⟩, ⟨scr.setWidth 64, 512⟩] s.wr)
    {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame [⟨st.setWidth 64, bufOff w⟩, ⟨scr.setWidth 64, 512⟩, below E 32] s.mem s'.mem →
      stateAt w s'.mem (st.setWidth 64) =
        compressBlocks P (stateAt w s.mem (st.setWidth 64)) s.mem (blk.setWidth 64) k
          (thi ++ tlo).toNat (lst != 0) → Q s') :
    WP isa (compressCall name code) s Q := by
  have fit : 4 * [Reg.ebp, .eax, .edx, .ecx, .edi, .esi, .ebx].length + 4 ≤ (s.gpr .esp).toNat := by
    rw [hesp]; simp only [List.length_cons, List.length_nil]; omega
  have hrs := frame_esp
  set sE := (pushed [Reg.ebp, .eax, .edx, .ecx, .edi, .esi, .ebx] s).callEntry with hsE
  have a0 : arg sE 0 = st := by rw [hsE, callEntry_arg fit hrs (by simp)]; simp [hS]
  have a1 : arg sE 1 = blk := by rw [hsE, callEntry_arg fit hrs (by simp)]; simp [hB]
  have a2 : (arg sE 2).toNat = k := by rw [hsE, callEntry_arg fit hrs (by simp)]; simp [hk]
  have a3 : arg sE 3 = tlo := by rw [hsE, callEntry_arg fit hrs (by simp)]; simp [hlo]
  have a4 : arg sE 4 = thi := by rw [hsE, callEntry_arg fit hrs (by simp)]; simp [hhi]
  have a5 : arg sE 5 = lst := by rw [hsE, callEntry_arg fit hrs (by simp)]; simp [hl]
  have a6 : arg sE 6 = scr := by rw [hsE, callEntry_arg fit hrs (by simp)]; simp [hC]
  have eA : argAddr sE 0 = (E - BitVec.ofNat 32 28).setWidth 64 := by
    rw [hsE, callEntry_argAddr0, hesp]; rfl
  have eSp : sE.gpr .esp = E - BitVec.ofNat 32 32 := by
    rw [hsE, callEntry_esp', hesp]; rfl
  have b28 : Region.Sub (below E 28) (below E 32) := below_sub (by omega) hE
  have r4 : Region.Sub ⟨(E - BitVec.ofNat 32 32).setWidth 64, 4⟩ (below E 32) := by
    have := below_inner (sp := E) (a := 4) (b := 32) (k := 28) (by omega) hE
    rw [show E - BitVec.ofNat 32 32 = E - BitVec.ofNat 32 28 - BitVec.ofNat 32 4 by
      rw [← VG.Offset.sub_add_eq]; rfl]
    exact this
  refine WP.callWith (k := compressX86 P) hf.verified hf.nosp frame_ne hrs
    (by rw [hf.stack, hesp]; simp only [List.length_cons, List.length_nil]; omega)
    (rd := [⟨blk.setWidth 64, blockBytes w * k⟩, ⟨argAddr sE 0, 28⟩])
    (wr := [⟨st.setWidth 64, 8 * (w / 8)⟩, ⟨scr.setWidth 64, 512⟩])
    ⟨?_, ?_, ?_⟩ fun s' rd' wr' cs' f' ⟨s₂, m₂, post⟩ => ?_
  · rw [← hsE]
    simp only [compressX86, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr,
      arg_withRegions, argAddr_withRegions, a0, a1, a2, a6, eA, eSp]
    refine ⟨trivial, trivial, d₁, d₂, d₃, dS.sub_left b28, dC.sub_left b28,
      dS.sub_left r4, dC.sub_left r4, f₀, f₁, f₃, ?_⟩
    rw [sub_toNat hE]; have := E.isLt; omega
  · rw [hesp]
    intro a n ⟨r, hr, hcn⟩
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · obtain ⟨r', hr', hc'⟩ := hc a n ⟨_, List.mem_singleton_self _, by simpa using hcn⟩
      exact InRegions_append_cons.mpr (.inr ⟨r', hr', hc'⟩)
    · refine InRegions_append_cons.mpr (.inl ?_)
      rw [eA] at hcn
      simp only [Region.Contains] at hcn ⊢
      simpa using hcn
    · obtain ⟨r', hr', hc'⟩ := hw a n ⟨_, by simp, hcn⟩
      exact InRegions_append_cons.mpr (.inr ⟨r', List.mem_append_right _ hr', hc'⟩)
    · obtain ⟨r', hr', hc'⟩ := hw a n ⟨_, by simp, hcn⟩
      exact InRegions_append_cons.mpr (.inr ⟨r', List.mem_append_right _ hr', hc'⟩)
  · rw [hesp]
    intro a n ⟨r, hr, hcn⟩
    obtain ⟨r', hr', hc'⟩ := hw a n ⟨r, hr, hcn⟩
    exact ⟨r', List.mem_cons_of_mem _ hr', hc'⟩
  · rw [hf.stack, hesp] at f'
    have hsE' : Frame [below E 32] s.mem sE.mem := by
      have := callEntry_frame fit hrs
      rw [hesp] at this; exact this
    rw [← hsE] at post
    simp only [compressX86, arg_withRegions, State.withRegions_mem, a0, a1, a2, a3, a4, a5, m₂] at post
    refine hQ s' rd' wr' cs' f' ?_
    have e₁ : stateAt w sE.mem (st.setWidth 64) = stateAt w s.mem (st.setWidth 64) :=
      stateAt_congr fun i hi =>
        hsE'.bytes (R := ⟨st.setWidth 64, bufOff w⟩) (by simpa using dS.symm) (by simp; omega) hi
    have e₂ : compressBlocks P (stateAt w s.mem (st.setWidth 64)) sE.mem (blk.setWidth 64) k
          (thi ++ tlo).toNat (lst != 0) =
        compressBlocks P (stateAt w s.mem (st.setWidth 64)) s.mem (blk.setWidth 64) k
          (thi ++ tlo).toNat (lst != 0) :=
      compressBlocks_congr P fun j hj =>
        hsE'.bytes (R := ⟨blk.setWidth 64, blockBytes w * k⟩) (by simpa using dB.symm) (by simp; omega) hj
    rw [post, e₁, e₂]

/-! ## Copying bytes into the buffer -/

theorem contains_prefix (q : Addr) {j k : Nat} (h : j ≤ k) : (⟨q, k⟩ : Region).Contains q j := by
  simp [Region.Contains, h]

/-- The copy loop's state after `j` of `k` bytes, from `s₀`. -/
structure CopyI (s₀ : State) (src dst cnt tmp : Reg) (dA sA : BitVec 32) (k j : Nat) (s : State) : Prop where
  j_le : j ≤ k
  srcV : s.gpr src = sA + BitVec.ofNat 32 j
  dstV : s.gpr dst = dA + BitVec.ofNat 32 j
  cntV : s.gpr cnt = BitVec.ofNat 32 (k - j)
  other : ∀ x, x ≠ src → x ≠ dst → x ≠ cnt → x ≠ tmp → s.gpr x = s₀.gpr x
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : s.mem = writeBytes s₀.mem (addr dA (bufOff w))
    ((bytesAt s₀.mem (sA.setWidth 64) k).take j)

/-- The loop copying `k ≥ 1` bytes from `sA` (at `src`) to `dA + N` (at `dst`),
with the count in `cnt` and the bytes through `tmp`: neither the source nor
the destination wraps around the (32-bit) address space, and they do not
overlap. -/
theorem copyLoop_ok {src dst cnt : Reg} {tmp : Reg8} (h₁ : src ≠ dst) (h₂ : src ≠ cnt)
    (h₃ : dst ≠ cnt) (h₄ : tmp.reg ≠ src) (h₅ : tmp.reg ≠ dst) (h₆ : tmp.reg ≠ cnt)
    {s₀ : State} {dA sA : BitVec 32} {k : Nat} (hk : 1 ≤ k) (hk32 : k < 2 ^ 32)
    (hfs : sA.toNat + k ≤ 2 ^ 32) (hfd : dA.toNat + bufOff w + k ≤ 2 ^ 32)
    (hsrc : s₀.gpr src = sA) (hdst : s₀.gpr dst = dA) (hcnt : s₀.gpr cnt = BitVec.ofNat 32 k)
    (hin : ∀ i < k, InRegions (s₀.rd ++ s₀.wr) (sA.setWidth 64 + BitVec.ofNat 64 i) 1)
    (hout : ∀ i < k, InRegions s₀.wr (addr dA (bufOff w) + BitVec.ofNat 64 i) 1)
    (hd : Region.Disjoint ⟨sA.setWidth 64, k⟩ ⟨addr dA (bufOff w), k⟩)
    {Q : State → Prop} (hQ : ∀ s, CopyI (w := w) s₀ src dst cnt tmp.reg dA sA k k s → Q s) :
    WP isa (copyLoop w src dst cnt tmp) s₀ Q := by
  refine WP.loop (M := isa) (fun n (s : State) => ∃ j, n = k - j ∧ j < k ∧
      CopyI (w := w) s₀ src dst cnt tmp.reg dA sA k j s) ?_ k s₀
    ⟨0, by omega, by omega, by omega, by simp [hsrc], by simp [hdst], by rw [hcnt, Nat.sub_zero],
      fun _ _ _ _ _ => rfl, rfl, rfl, by rw [List.take_zero, writeBytes_nil]⟩
  rintro n s ⟨j, rfl, hj, h⟩
  have hxs : (bytesAt s₀.mem (sA.setWidth 64) k).length = k := by simp [bytesAt]
  -- The addresses.
  have eS : addr (s.gpr src) 0 = sA.setWidth 64 + BitVec.ofNat 64 j := by
    rw [h.srcV, MdStream.X86.addr_add_ofNat (by omega), Nat.add_zero]
  have eD : addr (s.gpr dst) (bufOff w) = addr dA (bufOff w) + BitVec.ofNat 64 j := by
    rw [h.dstV, MdStream.X86.addr_add_ofNat (by omega), addr_eq (by omega), BitVec.add_assoc,
      BitVec.ofNat_add, BitVec.add_comm (BitVec.ofNat 64 j)]
  -- The byte read.
  have hin' : InRegions (s.rd ++ s.wr) (sA.setWidth 64 + BitVec.ofNat 64 j) 1 := by
    rw [h.rd, h.wr]; exact hin j hj
  have hbyte : s.mem (sA.setWidth 64 + BitVec.ofNat 64 j) = s₀.mem (sA.setWidth 64 + BitVec.ofNat 64 j) := by
    rw [h.mem]
    exact (writeBytes_frame s₀.mem _ _ (contains_prefix (k := k) _ (by simp; omega))).bytes
      (R := ⟨sA.setWidth 64, k⟩) (by simpa using hd) (by show k ≤ 2 ^ 64; omega) hj
  have hout' : InRegions s.wr (addr dA (bufOff w) + BitVec.ofNat 64 j) 1 := by
    rw [h.wr]; exact hout j hj
  refine cons (s' := s.setReg tmp.reg ((s.mem (sA.setWidth 64 + BitVec.ofNat 64 j)).setWidth 32))
    (by simp [exec, State.load8, ea_mk, at_, eS, hin']) ?_
  set s₁ := s.setReg tmp.reg ((s.mem (sA.setWidth 64 + BitVec.ofNat 64 j)).setWidth 32) with hs₁
  have g₁ : ∀ x, x ≠ tmp.reg → s₁.gpr x = s.gpr x := fun x hx => RegUpd.gpr_setReg_of_ne _ _ hx
  set m₂ := s₁.mem.writeW (addr dA (bufOff w) + BitVec.ofNat 64 j) ((s₁.gpr tmp.reg).setWidth 8) with hm₂
  refine cons (s' := { s₁ with mem := m₂ }) ?_ ?_
  · have e : s₁.ea (at_ dst (N w)) = addr dA (bufOff w) + BitVec.ofNat 64 j := by
      show addr (s₁.gpr dst) (N w) = _
      rw [g₁ _ (Ne.symm h₅)]; exact eD
    have hw₁ : InRegions s₁.wr (addr dA (bufOff w) + BitVec.ofNat 64 j) 1 := hout'
    simp only [exec, State.store8, e, hw₁, ite_true, hm₂]
  refine wp_addi fun s₃ u₃ => wp_addi fun s₄ u₄ => wp_subi fun s₅ u₅ _ hz₅ => WP.block_nil ?_
  have g : ∀ x, x ≠ cnt → x ≠ dst → x ≠ src → x ≠ tmp.reg → s₅.gpr x = s.gpr x := fun x a b c d => by
    rw [u₅.other x a, u₄.other x b, u₃.other x c]; exact g₁ x d
  have hcnt' : s₅.gpr cnt = BitVec.ofNat 32 (k - (j + 1)) := by
    rw [u₅.gpr, u₄.other _ (Ne.symm h₃), u₃.other _ (Ne.symm h₂), show s₁.gpr cnt = s.gpr cnt from
      g₁ _ (Ne.symm h₆), h.cntV, ofNat_pred (by omega), Nat.sub_sub]
  have hI : CopyI (w := w) s₀ src dst cnt tmp.reg dA sA k (j + 1) s₅ := by
    refine ⟨by omega, ?_, ?_, hcnt', fun x a b c d => ?_, ?_, ?_, ?_⟩
    · rw [u₅.other _ h₂, u₄.other _ h₁, u₃.gpr, show s₁.gpr src = s.gpr src from g₁ _ (Ne.symm h₄),
        h.srcV, BitVec.add_assoc, BitVec.ofNat_add]; rfl
    · rw [u₅.other _ h₃, u₄.gpr, u₃.other _ (Ne.symm h₁), show s₁.gpr dst = s.gpr dst from
        g₁ _ (Ne.symm h₅), h.dstV, BitVec.add_assoc, BitVec.ofNat_add]; rfl
    · rw [g x c b a d, h.other x a b c d]
    · rw [u₅.rd, u₄.rd, u₃.rd]; exact h.rd
    · rw [u₅.wr, u₄.wr, u₃.wr]; exact h.wr
    · have hj' : j < (bytesAt s₀.mem (sA.setWidth 64) k).length := by omega
      have hlen : (List.take j (bytesAt s₀.mem (sA.setWidth 64) k)).length < 2 ^ 64 := by
        simp only [List.length_take]; omega
      rw [u₅.mem, u₄.mem, u₃.mem]
      show s₁.mem.writeW _ ((s₁.gpr tmp.reg).setWidth 8) = _
      rw [hs₁, RegUpd.mem_setReg, RegUpd.gpr_setReg_self, hbyte, h.mem, List.take_add_one,
        List.getElem?_eq_getElem hj', Option.toList_some, writeBytes_snoc _ _ _ _ hlen]
      have hl : (List.take j (bytesAt s₀.mem (sA.setWidth 64) k)).length = j := by
        rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hj')]
      rw [hl, BitVec.setWidth_setWidth_of_le _ (by omega), BitVec.setWidth_eq]
      congr 1
      simp [bytesAt]
  have hzf : s₅.zf = some (decide (k - (j + 1) = 0)) := by
    rw [hz₅, u₄.other _ (Ne.symm h₃), u₃.other _ (Ne.symm h₂), show s₁.gpr cnt = s.gpr cnt from
      g₁ _ (Ne.symm h₆), h.cntV, ofNat_pred (show 1 ≤ k - j by omega), ofNat_beq_zero (by omega),
      show k - j - 1 = k - (j + 1) by omega]
  by_cases hjk : j + 1 = k
  · refine .inl ⟨?_, hQ _ (hjk ▸ hI)⟩
    simp only [eval, hzf, show k - (j + 1) = 0 by omega, decide_true, Option.map_some, Bool.not_true]
  · refine .inr ⟨?_, k - (j + 1), by omega, j + 1, rfl, by omega, hI⟩
    simp only [eval, hzf, show k - (j + 1) ≠ 0 by omega, decide_false, Option.map_some, Bool.not_false]

end VG.Proof.Blake2.X86.Stream
