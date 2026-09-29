import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx2.Setup

/-!
# ChaCha20 on x86-64 with AVX2: the constants

Untrusted: everything here is checked by Lean. The prologue stores the
rotation masks and the counter increments in `buf[128, 224)`, a quadword at
a time.
-/

namespace VG.Proof.ChaCha20.X86_64.Avx2

open VG VG.X86_64 VG.Impl.ChaCha20.X86_64.Avx2
open VG.Impl.ChaCha20.X86_64 (at_)

/-! ## Reading back quadwords -/

theorem readW_128 (m : Mem) (a : Addr) :
    m.readW a 128 = m.readW (a + BitVec.ofNat 64 8) 64 ++ m.readW a 64 := by
  have h1 : (m.readW a 128).extractLsb' 0 64 = m.readW a 64 := by
    have := readW_extract m a (w := 128) (k := 0) (n := 8) (by omega)
    simpa using this
  have h2 : (m.readW a 128).extractLsb' 64 64 = m.readW (a + BitVec.ofNat 64 8) 64 :=
    readW_extract m a (w := 128) (k := 8) (n := 8) (by omega)
  rw [← h1, ← h2]
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  by_cases h : i < 64
  · simp [h]
  · have e : 64 + (i - 64) = i := by omega
    simp only [h, decide_false, show i - 64 < 64 by omega, decide_true, Bool.true_and, e, ite_false]

theorem readW_256 (m : Mem) (a : Addr) :
    m.readW a 256 = m.readW (a + BitVec.ofNat 64 16) 128 ++ m.readW a 128 := by
  have h1 : (m.readW a 256).extractLsb' 0 128 = m.readW a 128 := by
    have := readW_extract m a (w := 256) (k := 0) (n := 16) (by omega)
    simpa using this
  have h2 : (m.readW a 256).extractLsb' 128 128 = m.readW (a + BitVec.ofNat 64 16) 128 :=
    readW_extract m a (w := 256) (k := 16) (n := 16) (by omega)
  rw [← h1, ← h2]
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  by_cases h : i < 128
  · simp [h]
  · have e : 128 + (i - 128) = i := by omega
    simp only [h, decide_false, show i - 128 < 128 by omega, decide_true, Bool.true_and, e, ite_false]

theorem readW64_off (m : Mem) (p : Addr) (v : BitVec 64) {d e : Nat} (hd : d < 2 ^ 32)
    (he : e < 2 ^ 32) (h : d + 8 ≤ e ∨ e + 8 ≤ d) :
    (m.writeW (p + BitVec.ofNat 64 e) v).readW (p + BitVec.ofNat 64 d) 64 =
      m.readW (p + BitVec.ofNat 64 d) 64 :=
  readW_writeW_off m p v (d := d) (e := e) (n := 8) (by omega) (by omega) (by omega)

/-! ## The stores -/

/-- The offsets in `buf` and values of the quadwords the prologue stores. -/
def constPairs : List (Nat × BitVec 64) :=
  [(128, 0x0504070601000302), (136, 0x0d0c0f0e09080b0a), (144, 0x0504070601000302),
   (152, 0x0d0c0f0e09080b0a), (160, 0x0605040702010003), (168, 0x0e0d0c0f0a09080b),
   (176, 0x0605040702010003), (184, 0x0e0d0c0f0a09080b), (192, 0x0000000100000000),
   (200, 0x0000000300000002), (208, 0x0000000500000004), (216, 0x0000000700000006)]

/-- Store each `(d, v)` at `buf + d`, through `rax`. -/
def pairsCode (ps : List (Nat × BitVec 64)) : List Instr :=
  ps.flatMap fun p => [.movImm64 .rax p.2, .store (at_ .rcx p.1) .rax]

theorem consts_eq : consts = pairsCode constPairs := by
  simp only [consts, storeQ, rot16Q, rot8Q, incQ, pairsCode, constPairs, rot16Off, rot8Off, incOff,
    List.length_cons, List.length_nil, List.range_succ, List.range_zero, List.nil_append,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, List.getD_cons_zero,
    List.getD_cons_succ, List.cons_append, List.nil_append, Nat.reduceAdd, Nat.reduceMul]

/-- Memory after the stores `ps`. -/
def storeAll (buf : Addr) (ps : List (Nat × BitVec 64)) (m : Mem) : Mem :=
  ps.foldl (fun m p => m.writeW (buf + BitVec.ofNat 64 p.1) p.2) m

theorem State.store64_eq (s : State) (a : Addr) (v : BitVec 64) :
    s.store64 a v = if InRegions s.wr a 8 then some (s.setMem (s.mem.writeW a v)) else none := by
  rw [State.store64]; rfl

theorem pairs_ok {buf : Addr} (ps : List (Nat × BitVec 64)) (hps : ∀ p ∈ ps, p.1 + 8 ≤ 320)
    {s : State} (hrcx : s.gpr .rcx = buf) (hb : bufR buf ∈ s.wr) :
    WP isa (.block (pairsCode ps)) s fun s' =>
      s'.mem = storeAll buf ps s.mem ∧ (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  induction ps generalizing s with
  | nil => exact WP.block_nil ⟨rfl, fun _ _ => rfl, rfl, rfl⟩
  | cons p ps ih =>
    have hp := hps p (List.mem_cons_self ..)
    have o := out_buf hb (d := p.1) (n := 8) hp
    rw [pairsCode, List.flatMap_cons, ← pairsCode]
    refine WP.block_append ?_
    apply WP.of_runBlock
    have g : (s.setReg .rax p.2).gpr .rcx = buf := by simp [State.setReg, hrcx]
    have o' : InRegions (s.setReg .rax p.2).wr (buf + BitVec.ofNat 64 p.1) 8 := o
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, ea_at, State.store64_eq, g, o',
      ite_true, Option.some.injEq, exists_eq_left']
    refine WP.mono (ih (fun q hq => hps q (List.mem_cons_of_mem _ hq)) (by simpa using g)
      (by exact hb)) fun s' ⟨m', g', r', w'⟩ => ⟨?_, fun r hr => ?_, r', w'⟩
    · rw [m', storeAll, storeAll, List.foldl_cons]; rfl
    · rw [g' r hr]; simp [State.setReg, hr]

theorem storeAll_frame {buf : Addr} {rs : List Region} (hr : bufR buf ∈ rs) (ps : List (Nat × BitVec 64))
    (hps : ∀ p ∈ ps, p.1 + 8 ≤ 320) (m : Mem) : Frame rs m (storeAll buf ps m) := by
  induction ps generalizing m with
  | nil => exact Frame.refl _ _
  | cons p ps ih =>
    rw [storeAll, List.foldl_cons, ← storeAll]
    exact ((Frame.refl _ _).writeW hr _ (bufR_contains buf (hps p (List.mem_cons_self ..)))).trans
      (ih (fun q hq => hps q (List.mem_cons_of_mem _ hq)) _)

/-! ## The constants -/

/-- A 256-bit read of four stored quadwords. -/
theorem read4 {m : Mem} {buf : Addr} {d : Nat} {v0 v1 v2 v3 : BitVec 64}
    (h0 : m.readW (buf + BitVec.ofNat 64 d) 64 = v0)
    (h1 : m.readW (buf + BitVec.ofNat 64 (d + 8)) 64 = v1)
    (h2 : m.readW (buf + BitVec.ofNat 64 (d + 16)) 64 = v2)
    (h3 : m.readW (buf + BitVec.ofNat 64 (d + 24)) 64 = v3) :
    m.readW (buf + BitVec.ofNat 64 d) 256 = (v3 ++ v2) ++ (v1 ++ v0) := by
  rw [readW_256, readW_128, readW_128]
  simp only [add_ofNat, Nat.add_assoc, Nat.reduceAdd]
  rw [h0, h1, h2, h3]

/-- Read back a stored quadword. -/
local macro "qread" : tactic => `(tactic|
  simp (disch := decide) only [storeAll, constPairs, List.foldl_cons, List.foldl_nil, Nat.reduceAdd,
    readW64_off, Mem.readW_writeW_self64])

theorem consts_mem (m : Mem) (buf : Addr) : Consts (storeAll buf constPairs m) buf := by
  have R16 := read4 (m := storeAll buf constPairs m) (buf := buf) (d := 128)
    (v0 := 0x0504070601000302) (v1 := 0x0d0c0f0e09080b0a) (v2 := 0x0504070601000302)
    (v3 := 0x0d0c0f0e09080b0a) (by qread) (by qread) (by qread) (by qread)
  have R8 := read4 (m := storeAll buf constPairs m) (buf := buf) (d := 160)
    (v0 := 0x0605040702010003) (v1 := 0x0e0d0c0f0a09080b) (v2 := 0x0605040702010003)
    (v3 := 0x0e0d0c0f0a09080b) (by qread) (by qread) (by qread) (by qread)
  have RI := read4 (m := storeAll buf constPairs m) (buf := buf) (d := 192)
    (v0 := 0x0000000100000000) (v1 := 0x0000000300000002) (v2 := 0x0000000500000004)
    (v3 := 0x0000000700000006) (by qread) (by qread) (by qread) (by qread)
  refine ⟨by rw [R16]; decide, by rw [R16]; decide, ⟨by rw [R8]; decide, by rw [R8]; decide⟩,
    fun l q hl hq => ?_⟩
  have E := readW_extract (storeAll buf constPairs m) (buf + BitVec.ofNat 64 192) (w := 256)
    (k := 16 * l + 4 * q) (n := 4) (by omega)
  rw [add_ofNat] at E
  refine E.symm.trans ?_
  rw [RI]
  rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;>
    rcases (by omega : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3) with rfl | rfl | rfl | rfl <;> decide

end VG.Proof.ChaCha20.X86_64.Avx2
