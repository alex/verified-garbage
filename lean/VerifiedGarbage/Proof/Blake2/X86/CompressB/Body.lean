import VerifiedGarbage.Proof.Blake2.X86.CompressB.Pre
import VerifiedGarbage.Proof.Framework.Range

/-!
# BLAKE2b compression function on x86 (32-bit): the parts of one block

Copying 32-bit words (`copyWords_ok`), which copies the block and the state
into `scratch`; initializing the rest of the work vector (`ivWord_ok`,
`ivXor_ok`); XORing the work vector into the state (`finish_ok`); and
advancing the parameters to the next block (`advance_ok`).
-/

namespace VG.Proof.Blake2.X86.CompressB

open VG VG.X86 VG.Impl.Blake2.X86.CompressB
open VG.Spec.Blake2 (HashValue Work Block stateAt blockAt)
open VG.Proof.Sha512.X86 (Acc rd64 write64 mem_rd readSrc_mem ea_of wp_movS wp_xorS wp_addS
  wp_adcS lo_rd64 hi_rd64 rd64_write64_self rd64_write64_ne)
open VG.Proof.Sha512.Word64 (lo hi readW64 lo_append hi_append hi_append_lo lo_xor hi_xor)
open VG.Proof.Sha256.X86.Stream (contains_addr Upd Mupd wp_movm wp_store wp_movi wp_subi
  readW_writeW_addr)

/-! ## 64-bit words in `scratch` -/

section
variable {B : BitVec 32} (hfit : B.toNat + 512 ≤ 2 ^ 32)
include hfit

theorem rw64_ne (m : Mem) (x : BitVec 64) {o o' : Nat} (h : o + 8 ≤ 512) (h' : o' + 8 ≤ 512)
    (hs : Sep8 o o') : rd64 (write64 m B o x) B o' = rd64 m B o' :=
  rd64_write64_ne m x (by omega) (by omega) hs

theorem rw64_self (m : Mem) (x : BitVec 64) {o : Nat} (h : o + 8 ≤ 512) :
    rd64 (write64 m B o x) B o = x :=
  rd64_write64_self m x (by omega)

theorem rw32_ne (m : Mem) (x : BitVec 32) {o o' : Nat} (h : o + 4 ≤ 512) (h' : o' + 4 ≤ 512)
    (hs : o + 4 ≤ o' ∨ o' + 4 ≤ o) : (m.writeW (addr B o) x).readW (addr B o') 32 = m.readW (addr B o') 32 :=
  readW_writeW_addr m x (by omega) (by omega) hs.symm

end

/-- A 64-bit word in memory, as its halves. -/
theorem rd64_eq {m : Mem} {x : BitVec 32} {o : Nat} (h : x.toNat + o + 8 ≤ 2 ^ 32) :
    rd64 m x o = m.readW (x.setWidth 64 + BitVec.ofNat 64 o) 64 := by
  rw [readW64, show x.setWidth 64 + BitVec.ofNat 64 o + 4 = x.setWidth 64 + BitVec.ofNat 64 (o + 4) from
      Offset.add_ofNat_add_ofNat _ _ 4, ← addr_eq (by omega), ← addr_eq (by omega)]
  rfl

theorem stateAt_rd64 {x : BitVec 32} (hfit : x.toNat + 64 ≤ 2 ^ 32) (m : Mem) {k : Nat} (hk : k < 8) :
    (stateAt 64 m (x.setWidth 64))[k] = rd64 m x (8 * k) := by
  simp only [stateAt, Vector.getElem_ofFn]
  rw [rd64_eq (by omega)]

/-! ## Copying words -/

/-- Copying `n` words `[src + so + 4j]` to `[esi + d + 4j]`, through `eax`, into
the region `R`, which the words copied are outside of. -/
theorem copyWords_ok {src : Reg} (hsrc : src ≠ .eax) {S D : BitVec 32} {so d n : Nat} {R : Region}
    {s : State} (hS : s.gpr src = S) (hD : s.gpr .esi = D) (hfit : D.toNat + d + 4 * n ≤ 2 ^ 32)
    (hin : ∀ j < n, InRegions (s.rd ++ s.wr) (addr S (so + 4 * j)) 4)
    (hout : ∀ j < n, InRegions s.wr (addr D (d + 4 * j)) 4)
    (hR : ∀ j < n, R.Contains (addr D (d + 4 * j)) 4)
    (hdis : ∀ j < n, Region.Disjoint ⟨addr S (so + 4 * j), 4⟩ R) :
    WP isa (.block (copyWords src so d n)) s fun s' =>
      (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [R] s.mem s'.mem ∧
      ∀ j < n, s'.mem.readW (addr D (d + 4 * j)) 32 = s.mem.readW (addr S (so + 4 * j)) 32 := by
  unfold copyWords
  refine wp_range_flatMap (M := isa) (fun k (s' : State) => (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ Frame [R] s.mem s'.mem ∧
      ∀ j < k, s'.mem.readW (addr D (d + 4 * j)) 32 = s.mem.readW (addr S (so + 4 * j)) 32)
    (fun k s' hk ⟨hg, hrd, hwr, hf, hc⟩ => ?_) n (Nat.le_refl _) s
    ⟨fun _ _ => rfl, rfl, rfl, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  refine wp_movm (ea_of ((hg src hsrc).trans hS) _) (by rw [hrd, hwr]; exact hin k hk)
    fun s₁ u₁ => ?_
  refine wp_store (ea_of (by rw [u₁.other _ (by decide), hg _ (by decide), hD]) _)
    (by rw [u₁.wr, hwr]; exact hout k hk) fun s₂ u₂ => WP.block_nil ?_
  have hv : s'.mem.readW (addr S (so + 4 * k)) 32 = s.mem.readW (addr S (so + 4 * k)) 32 :=
    hf.readW (Region.contains_self _ _) (by simpa using hdis k hk) (by decide)
  refine ⟨fun r hr => by rw [u₂.gpr, u₁.other r hr, hg r hr], by rw [u₂.rd, u₁.rd, hrd],
    by rw [u₂.wr, u₁.wr, hwr], ?_, fun j hj => ?_⟩
  · rw [u₂.mem, u₁.mem]; exact hf.writeW (List.mem_singleton_self _) _ (hR k hk)
  · rw [u₂.mem, u₁.gpr, u₁.mem]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [readW_writeW_addr _ _ (by omega) (by omega) (by omega)]; exact hc j hj
    · rw [Mem.readW_writeW_self32, hv]

/-! ## The rest of the work vector -/

section
variable {rest : List Instr} {Q : State → Prop} {B : BitVec 32} {s : State}

theorem ivWord_ok (hD : s.gpr .esi = B) (hA : Acc s.wr B 512) {k : Nat} (hk : vOff k + 8 ≤ 512)
    (v : BitVec 64)
    (K : ∀ s', (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr →
      s'.mem = write64 s.mem B (vOff k) v → WP isa (.block rest) s' Q) :
    WP isa (.block (ivWord k v ++ rest)) s Q := by
  simp only [ivWord, List.cons_append, List.nil_append]
  refine wp_movi fun s₁ u₁ => wp_store (ea_of (by rw [u₁.other _ (by decide), hD]) _)
    (by rw [u₁.wr]; exact hA _ (by omega)) fun s₂ u₂ => wp_movi fun s₃ u₃ =>
    wp_store (ea_of (by rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), hD]) _)
    (by rw [u₃.wr, u₂.wr, u₁.wr]; exact hA _ (by omega)) fun s₄ u₄ => K s₄ ?_ ?_ ?_ ?_
  · intro r hr; rw [u₄.gpr, u₃.other r hr, u₂.gpr, u₁.other r hr]
  · rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  · rw [u₄.mem, u₃.gpr, u₃.mem, u₂.mem, u₁.gpr, u₁.mem]; rfl

theorem ivXor_ok (hD : s.gpr .esi = B) (hA : Acc s.wr B 512) (hfit : B.toNat + 512 ≤ 2 ^ 32)
    {k o : Nat} (hk : vOff k + 8 ≤ 512) (ho : o + 8 ≤ 512) (hs : Sep8 (vOff k) o) (v : BitVec 64)
    (K : ∀ s', (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr →
      s'.mem = write64 s.mem B (vOff k) (v ^^^ rd64 s.mem B o) → WP isa (.block rest) s' Q) :
    WP isa (.block (ivXor k v o ++ rest)) s Q := by
  simp only [ivXor, List.cons_append, List.nil_append]
  refine wp_movi fun s₁ u₁ => ?_
  refine wp_xorS (readSrc_mem (by rw [u₁.other _ (by decide), hD])
    (by rw [u₁.rd, u₁.wr]; exact mem_rd (hA _ (by omega)))) fun s₂ u₂ => ?_
  refine wp_store (ea_of (by rw [u₂.other _ (by decide), u₁.other _ (by decide), hD]) _)
    (by rw [u₂.wr, u₁.wr]; exact hA _ (by omega)) fun s₃ u₃ => wp_movi fun s₄ u₄ => ?_
  have h₄ : s₄.gpr .esi = B := by
    rw [u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), hD]
  have w₄ : s₄.wr = s.wr := by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  have r₄ : s₄.rd = s.rd := by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  refine wp_xorS (readSrc_mem h₄ (by rw [r₄, w₄]; exact mem_rd (hA _ (by omega))))
    fun s₅ u₅ => ?_
  refine wp_store (ea_of (by rw [u₅.other _ (by decide), h₄]) _)
    (by rw [u₅.wr, w₄]; exact hA _ (by omega)) fun s₆ u₆ => K s₆ ?_ ?_ ?_ ?_
  · intro r hr
    rw [u₆.gpr, u₅.other r hr, u₄.other r hr, u₃.gpr, u₂.other r hr, u₁.other r hr]
  · rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₆.wr, u₅.wr, w₄]
  · rw [u₆.mem, u₅.gpr, u₅.mem, u₄.gpr, u₄.mem, u₃.mem, u₂.gpr, u₁.gpr, u₂.mem, u₁.mem,
      readW_writeW_addr _ _ (by omega) (by omega) (by simp only [Sep8] at hs; omega)]
    simp only [write64, rd64, lo_xor, hi_xor, lo_append, hi_append]
    rfl

end

/-! ## XORing the work vector into the state -/

/-- After `n` words of `finish`, from the state `s₁`. -/
structure FI (s₀ s₁ : State) (n : Nat) (s : State) : Prop where
  gpr : ∀ r, r ≠ .eax → s.gpr r = s₁.gpr r
  rd : s.rd = s₁.rd
  wr : s.wr = s₁.wr
  frame : Frame [stR s₀] s₁.mem s.mem
  words : ∀ j < 16, s.mem.readW (addr (st s₀) (4 * j)) 32 =
    if j < n then s₁.mem.readW (addr (st s₀) (4 * j)) 32 ^^^
      s₁.mem.readW (addr (scr s₀) (vOff 0 + 4 * j)) 32 ^^^
      s₁.mem.readW (addr (scr s₀) (vOff 8 + 4 * j)) 32
    else s₁.mem.readW (addr (st s₀) (4 * j)) 32

theorem finishWord_ok {s₀ : State} (hp : Pre s₀) {s₁ : State} (hc : s₁.gpr .ecx = st s₀)
    (he : s₁.gpr .esi = scr s₀) (hrd : s₁.rd = s₀.rd) (hwr : s₁.wr = s₀.wr) (n : Nat) (hn : n < 16)
    (s : State) (hf : FI s₀ s₁ n s) :
    WP isa (.block (finishWord n)) s (FI s₀ s₁ (n + 1)) := by
  have fS := hp.st_fits
  have fV := hp.scr_fits
  have hw : s.wr = s₀.wr := hf.wr.trans hwr
  have hsc : s.gpr .ecx = st s₀ := (hf.gpr _ (by decide)).trans hc
  have hsi : s.gpr .esi = scr s₀ := (hf.gpr _ (by decide)).trans he
  -- The scratch words are unchanged.
  have kv : ∀ d, d + 4 ≤ 512 → s.mem.readW (addr (scr s₀) d) 32 = s₁.mem.readW (addr (scr s₀) d) 32 :=
    fun d hd => hf.frame.readW (contains_addr (len := 512) hd (by omega) fV)
      (by simpa using hp.st_scr.symm) (by decide)
  simp only [finishWord]
  refine wp_movm (ea_of hsc _) (by rw [hf.rd, hrd, hw]; exact hp.in_st rfl (by omega))
    fun s₂ u₂ => ?_
  refine wp_xorS (readSrc_mem (by rw [u₂.other _ (by decide), hsi])
    (by rw [u₂.rd, u₂.wr, hf.rd, hrd, hw]; exact hp.in_scr rfl (by simp only [vOff]; omega)))
    fun s₃ u₃ => ?_
  refine wp_xorS (readSrc_mem (by rw [u₃.other _ (by decide), u₂.other _ (by decide), hsi])
    (by rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr, hf.rd, hrd, hw]; exact hp.in_scr rfl (by simp only [vOff]; omega)))
    fun s₄ u₄ => ?_
  refine wp_store (ea_of (by rw [u₄.other _ (by decide), u₃.other _ (by decide),
    u₂.other _ (by decide), hsc]) _) (by rw [u₄.wr, u₃.wr, u₂.wr, hw]; exact hp.accS rfl _ (by omega))
    fun s₅ u₅ => WP.block_nil ?_
  have hv : s₅.mem = s.mem.writeW (addr (st s₀) (4 * n))
      (s.mem.readW (addr (st s₀) (4 * n)) 32 ^^^ s.mem.readW (addr (scr s₀) (vOff 0 + 4 * n)) 32 ^^^
        s.mem.readW (addr (scr s₀) (vOff 8 + 4 * n)) 32) := by
    rw [u₅.mem, u₄.gpr, u₄.mem, u₃.gpr, u₃.mem, u₂.gpr, u₂.mem]
  refine ⟨fun r hr => ?_, by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, hf.rd],
    by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, hf.wr], ?_, fun j hj => ?_⟩
  · rw [u₅.gpr, u₄.other r hr, u₃.other r hr, u₂.other r hr, hf.gpr r hr]
  · rw [hv]
    exact hf.frame.writeW (List.mem_singleton_self _) _ (contains_addr (by omega) (by omega) fS)
  · rw [hv]
    rcases Nat.lt_or_ge j n with hjn | hjn
    · rw [readW_writeW_addr _ _ (by omega) (by omega) (by omega), hf.words j hj]
      simp only [hjn, show j < n + 1 by omega, ite_true]
    · rcases Nat.eq_or_lt_of_le hjn with rfl | hjn'
      · rw [Mem.readW_writeW_self32, hf.words _ hj, kv _ (by simp only [vOff]; omega),
          kv _ (by simp only [vOff]; omega)]
        simp only [Nat.lt_irrefl, ite_false, Nat.lt_succ_self, ite_true]
      · rw [readW_writeW_addr _ _ (by omega) (by omega) (by omega), hf.words j hj]
        simp only [show ¬ j < n by omega, show ¬ j < n + 1 by omega, ite_false]

theorem finishWords_ok {s₀ : State} (hp : Pre s₀) {s₁ : State} (hc : s₁.gpr .ecx = st s₀)
    (he : s₁.gpr .esi = scr s₀) (hrd : s₁.rd = s₀.rd) (hwr : s₁.wr = s₀.wr) :
    WP isa (.block ((List.range 16).flatMap finishWord)) s₁ (FI s₀ s₁ 16) :=
  wp_range_flatMap (M := isa) (FI s₀ s₁) (fun k s hk h => finishWord_ok hp hc he hrd hwr k hk s h) 16
    (Nat.le_refl _) s₁ ⟨fun _ _ => rfl, rfl, rfl, Frame.refl _ _, fun j _ => by
      simp only [Nat.not_lt_zero, ite_false]⟩

/-- The state after `finish`, word by word. -/
theorem FI.state {s₀ s₁ s : State} (hf : FI s₀ s₁ 16 s) {k : Nat} (hk : k < 8) :
    rd64 s.mem (st s₀) (8 * k) = rd64 s₁.mem (st s₀) (8 * k) ^^^ rd64 s₁.mem (scr s₀) (vOff k) ^^^
      rd64 s₁.mem (scr s₀) (vOff (k + 8)) := by
  have e₀ := hf.words (2 * k) (by omega)
  have e₁ := hf.words (2 * k + 1) (by omega)
  rw [ite_eq_left_iff.mpr (fun h => absurd (by omega) h)] at e₀ e₁
  rw [show vOff 0 + 4 * (2 * k) = vOff k by simp only [vOff]; omega,
    show vOff 8 + 4 * (2 * k) = vOff (k + 8) by simp only [vOff]; omega,
    show 4 * (2 * k) = 8 * k by omega] at e₀
  rw [show vOff 0 + 4 * (2 * k + 1) = vOff k + 4 by simp only [vOff]; omega,
    show vOff 8 + 4 * (2 * k + 1) = vOff (k + 8) + 4 by simp only [vOff]; omega,
    show 4 * (2 * k + 1) = 8 * k + 4 by omega] at e₁
  rw [← hi_append_lo (rd64 s₁.mem (st s₀) (8 * k) ^^^ _ ^^^ _), hi_xor, hi_xor, lo_xor, lo_xor,
    hi_rd64, hi_rd64, hi_rd64, lo_rd64, lo_rd64, lo_rd64, ← e₀, ← e₁]
  rfl

/-! ## Advancing to the next block -/

section
variable {rest : List Instr} {Q : State → Prop} {s : State}

theorem wp_movC {d : Reg} {src : Src} {v : BitVec 32} (h : readSrc s src = some v)
    (k : ∀ s', Upd s s' d v → s'.cf = s.cf → WP isa (.block rest) s' Q) :
    WP isa (.block (.mov d src :: rest)) s Q :=
  Proof.Sha256.X86.Stream.WP.cons (s' := s.setReg d v) (by simp [exec, h])
    (k _ (Upd.setReg _ _ _) rfl)

theorem wp_storeC {m : MemOp} {r : Reg} {a : Addr} (ha : s.ea m = a) (hout : InRegions s.wr a 4)
    (k : ∀ s', Mupd s s' (s.mem.writeW a (s.gpr r)) → s'.cf = s.cf → s'.zf = s.zf →
      WP isa (.block rest) s' Q) :
    WP isa (.block (.store m r :: rest)) s Q := by
  refine Proof.Sha256.X86.Stream.WP.cons (s' := { s with mem := s.mem.writeW a (s.gpr r) }) ?_
    (k _ ⟨rfl, rfl, rfl, rfl⟩ rfl rfl)
  simp [exec, State.store32, ha, hout]

theorem wp_adcC {d : Reg} {v : BitVec 32} {c : Bool} (hc : s.cf = some c)
    (k : ∀ s', Upd s s' d (s.gpr d + v + (BitVec.ofBool c).setWidth 32) →
      s'.cf = some (decide (2 ^ 32 ≤ (s.gpr d).toNat + v.toNat + c.toNat)) →
      WP isa (.block rest) s' Q) :
    WP isa (.block (.alu .adc d (.imm v) :: rest)) s Q :=
  Proof.Sha256.X86.Stream.WP.cons (by simp [exec, execAlu, readSrc, hc]; rfl)
    (k _ (Upd.flags _ _ _ _ _ _) rfl)

theorem wp_addC {d : Reg} {v : BitVec 32}
    (k : ∀ s', Upd s s' d (s.gpr d + v) → s'.cf = some (decide (2 ^ 32 ≤ (s.gpr d).toNat + v.toNat)) →
      WP isa (.block rest) s' Q) :
    WP isa (.block (.alu .add d (.imm v) :: rest)) s Q :=
  Proof.Sha256.X86.Stream.WP.cons rfl (k _ (Upd.flags _ _ _ _ _ _) rfl)

end

/-- The parameters after `advance`: the block's address and the 128-bit
counter advanced by 128 bytes, and the count of blocks decremented. -/
def advMem (B : BitVec 32) (m : Mem) : Mem :=
  let T0 := m.readW (addr B tOff) 32
  let T1 := m.readW (addr B (tOff + 4)) 32
  let T2 := m.readW (addr B (tOff + 8)) 32
  let T3 := m.readW (addr B (tOff + 12)) 32
  let c0 := decide (2 ^ 32 ≤ T0.toNat + (128 : BitVec 32).toNat)
  let c1 := decide (2 ^ 32 ≤ T1.toNat + (0 : BitVec 32).toNat + c0.toNat)
  let c2 := decide (2 ^ 32 ≤ T2.toNat + (0 : BitVec 32).toNat + c1.toNat)
  ((((((m.writeW (addr B blOff) (m.readW (addr B blOff) 32 + 128)).writeW (addr B tOff)
    (T0 + 128)).writeW (addr B (tOff + 4)) (T1 + 0 + (BitVec.ofBool c0).setWidth 32)).writeW
    (addr B (tOff + 8)) (T2 + 0 + (BitVec.ofBool c1).setWidth 32)).writeW (addr B (tOff + 12))
    (T3 + 0 + (BitVec.ofBool c2).setWidth 32)).writeW (addr B nOff) (m.readW (addr B nOff) 32 - 1))

theorem advance_ok {B : BitVec 32} (hfit : B.toNat + 512 ≤ 2 ^ 32) {s : State}
    (hD : s.gpr .esi = B) (hA : Acc s.wr B 512) :
    WP isa (.block advance) s fun s' =>
      s'.mem = advMem B s.mem ∧ s'.zf = some (s.mem.readW (addr B nOff) 32 - 1 == 0) ∧
      (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have r32 := rw32_ne hfit
  have inr : ∀ (rs : List Region) (o : Nat), o + 4 ≤ 512 → InRegions (rs ++ s.wr) (addr B o) 4 :=
    fun rs o ho => let ⟨r, hr, hc⟩ := hA o ho; ⟨r, List.mem_append_right _ hr, hc⟩
  unfold advance
  -- The block's address.
  refine wp_movm (ea_of hD _) (mem_rd (hA blOff (by decide))) fun s₁ u₁ => ?_
  refine wp_addC fun s₂ u₂ _ => ?_
  have e₂ : s₂.gpr .esi = B := by rw [u₂.other _ (by decide), u₁.other _ (by decide), hD]
  have w₂ : s₂.wr = s.wr := by rw [u₂.wr, u₁.wr]
  refine wp_storeC (ea_of e₂ _) (by rw [w₂]; exact hA blOff (by decide)) fun s₃ u₃ _ _ => ?_
  -- The counter.
  refine wp_movm (ea_of (by rw [u₃.gpr, e₂]) _) (by rw [u₃.wr, w₂]; exact inr _ tOff (by decide))
    fun s₄ u₄ => ?_
  refine wp_addC fun s₅ u₅ c₅ => ?_
  have e₅ : s₅.gpr .esi = B := by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, e₂]
  have w₅ : s₅.wr = s.wr := by rw [u₅.wr, u₄.wr, u₃.wr, w₂]
  refine wp_storeC (ea_of e₅ _) (by rw [w₅]; exact hA tOff (by decide)) fun s₆ u₆ f₆ _ => ?_
  refine wp_movC (readSrc_mem (by rw [u₆.gpr, e₅]) (by rw [u₆.wr, w₅]; exact inr _ (tOff + 4) (by decide)))
    fun s₇ u₇ f₇ => ?_
  refine wp_adcC (f₇.trans (f₆.trans c₅)) fun s₈ u₈ c₈ => ?_
  have e₈ : s₈.gpr .esi = B := by rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, e₅]
  have w₈ : s₈.wr = s.wr := by rw [u₈.wr, u₇.wr, u₆.wr, w₅]
  refine wp_storeC (ea_of e₈ _) (by rw [w₈]; exact hA (tOff + 4) (by decide)) fun s₉ u₉ f₉ _ => ?_
  refine wp_movC (readSrc_mem (by rw [u₉.gpr, e₈]) (by rw [u₉.wr, w₈]; exact inr _ (tOff + 8) (by decide)))
    fun s₁₀ u₁₀ f₁₀ => ?_
  refine wp_adcC (f₁₀.trans (f₉.trans c₈)) fun s₁₁ u₁₁ c₁₁ => ?_
  have e₁₁ : s₁₁.gpr .esi = B := by rw [u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.gpr, e₈]
  have w₁₁ : s₁₁.wr = s.wr := by rw [u₁₁.wr, u₁₀.wr, u₉.wr, w₈]
  refine wp_storeC (ea_of e₁₁ _) (by rw [w₁₁]; exact hA (tOff + 8) (by decide)) fun s₁₂ u₁₂ f₁₂ _ => ?_
  refine wp_movC (readSrc_mem (by rw [u₁₂.gpr, e₁₁]) (by rw [u₁₂.wr, w₁₁]; exact inr _ (tOff + 12) (by decide)))
    fun s₁₃ u₁₃ f₁₃ => ?_
  refine wp_adcC (f₁₃.trans (f₁₂.trans c₁₁)) fun s₁₄ u₁₄ _ => ?_
  have e₁₄ : s₁₄.gpr .esi = B := by rw [u₁₄.other _ (by decide), u₁₃.other _ (by decide), u₁₂.gpr, e₁₁]
  have w₁₄ : s₁₄.wr = s.wr := by rw [u₁₄.wr, u₁₃.wr, u₁₂.wr, w₁₁]
  refine wp_storeC (ea_of e₁₄ _) (by rw [w₁₄]; exact hA (tOff + 12) (by decide)) fun s₁₅ u₁₅ _ _ => ?_
  -- The count.
  refine wp_movm (ea_of (by rw [u₁₅.gpr, e₁₄]) _)
    (by rw [u₁₅.wr, w₁₄]; exact inr _ nOff (by decide)) fun s₁₆ u₁₆ => ?_
  refine wp_subi fun s₁₇ u₁₇ z₁₇ => ?_
  have e₁₇ : s₁₇.gpr .esi = B := by rw [u₁₇.other _ (by decide), u₁₆.other _ (by decide), u₁₅.gpr, e₁₄]
  have w₁₇ : s₁₇.wr = s.wr := by rw [u₁₇.wr, u₁₆.wr, u₁₅.wr, w₁₄]
  refine wp_storeC (ea_of e₁₇ _) (by rw [w₁₇]; exact hA nOff (by decide)) fun s₁₈ u₁₈ _ z₁₈ =>
    WP.block_nil ⟨?_, ?_, fun r hr => ?_, ?_, ?_⟩
  · simp (disch := decide) only [advMem, u₁₈.mem, u₁₇.gpr, u₁₇.mem, u₁₆.gpr, u₁₆.mem,
      u₁₅.mem, u₁₄.gpr, u₁₄.mem, u₁₃.gpr, u₁₃.mem, u₁₂.mem, u₁₁.gpr, u₁₁.mem,
      u₁₀.gpr, u₁₀.mem, u₉.mem, u₈.gpr, u₈.mem, u₇.gpr, u₇.mem, u₆.mem, u₅.gpr,
      u₅.mem, u₄.gpr, u₄.mem, u₃.mem, u₂.gpr, u₂.mem, u₁.gpr, u₁.mem, r32]
  · rw [z₁₈, z₁₇]
    simp (disch := decide) only [u₁₆.gpr, u₁₅.mem, u₁₄.mem, u₁₃.mem, u₁₂.mem, u₁₁.mem, u₁₀.mem,
      u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem, r32]
  · rw [u₁₈.gpr, u₁₇.other r hr, u₁₆.other r hr, u₁₅.gpr, u₁₄.other r hr, u₁₃.other r hr, u₁₂.gpr,
      u₁₁.other r hr, u₁₀.other r hr, u₉.gpr, u₈.other r hr, u₇.other r hr, u₆.gpr, u₅.other r hr,
      u₄.other r hr, u₃.gpr, u₂.other r hr, u₁.other r hr]
  · rw [u₁₈.rd, u₁₇.rd, u₁₆.rd, u₁₅.rd, u₁₄.rd, u₁₃.rd, u₁₂.rd, u₁₁.rd, u₁₀.rd, u₉.rd, u₈.rd,
      u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₁₈.wr, w₁₇]

end VG.Proof.Blake2.X86.CompressB
