import VerifiedGarbage.Proof.Blake2.X86.Stream.Common
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Sha512.Word64

/-!
# Streaming BLAKE2 on x86 (32-bit): `init`

`init` copies the key, if any, into the zeroed buffer (`keyBlock_ok`), keeping
our caller's `ebx` in the first word of the hash value meanwhile, then stores
the initial hash value (`initState_ok`), for either word size.
-/

namespace VG.Proof.Blake2.X86.Stream.Init

open VG VG.X86 VG.X86.Wp VG.Spec.Blake2
open VG.Impl.Blake2.X86 (at_)
open VG.Impl.Blake2.X86.Stream
open VG.Proof.Blake2 (initX86 repr_keyBlock stateAt_congr bytesAt_congr bytesAt_add)
open VG.WriteBytes (writeBytes writeBytes_nil writeBytes_snoc writeBytes_frame writeBytes_append
  writeBytes_before write_eq_writeBytes)
open VG.Proof.MdStream.X86 (contains_addr sub_offset contains_offset)

variable {w : Nat} {P : Params w}

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev esp₀ : BitVec 32 := s₀.gpr .esp
abbrev st : BitVec 32 := arg s₀ 0
abbrev nn : Nat := (arg s₀ 1).toNat
abbrev key : BitVec 32 := arg s₀ 2
abbrev kk : Nat := (arg s₀ 3).toNat
abbrev stA : Addr := (st s₀).setWidth 64
abbrev keyA : Addr := (key s₀).setWidth 64
abbrev stR (w : Nat) : Region := ⟨stA s₀, bufOff w + blockBytes w⟩
abbrev keyR : Region := ⟨keyA s₀, kk s₀⟩
abbrev argR : Region := ⟨argAddr s₀ 0, 16⟩
abbrev retR : Region := ⟨(esp₀ s₀).setWidth 64, 4⟩
/-- The key. -/
abbrev K : List Byte := bytesAt s₀.mem (keyA s₀) (kk s₀)

end

structure Pre (P : Params w) (s₀ : State) : Prop where
  rd : s₀.rd = [keyR s₀, argR s₀]
  wr : s₀.wr = [stR s₀ w]
  key_st : (keyR s₀).Disjoint (stR s₀ w)
  a_st : (argR s₀).Disjoint (stR s₀ w)
  ret_st : (retR s₀).Disjoint (stR s₀ w)
  st_fit : (st s₀).toNat + (bufOff w + blockBytes w) ≤ 2 ^ 32
  key_fit : (key s₀).toNat + kk s₀ ≤ 2 ^ 32
  sp_fit : (esp₀ s₀).toNat + 20 ≤ 2 ^ 32
  nn_lo : 1 ≤ nn s₀
  nn_hi : nn s₀ ≤ P.maxBytes
  kk_hi : kk s₀ ≤ P.maxBytes

theorem pre_of {s₀ : State} (h : (initX86 P).pre s₀) : Pre P s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩

namespace Pre
variable {s₀ : State} (hp : Pre P s₀)
include hp

theorem arg_in {d : Nat} (hd₁ : 4 ≤ d) (hd : d + 4 ≤ 20) : (argR s₀).Contains (addr (esp₀ s₀) d) 4 := by
  have := hp.sp_fit
  show (⟨addr (esp₀ s₀) 4, 16⟩ : Region).Contains _ _
  rw [addr_eq (by omega), addr_eq (by omega)]
  exact Offset.contains _ hd₁ (by omega) (by omega)

theorem arg_sub {d : Nat} (hd₁ : 4 ≤ d) (hd : d + 4 ≤ 20) : Region.Sub ⟨addr (esp₀ s₀) d, 4⟩ (argR s₀) := by
  have := hp.sp_fit
  show Region.Sub _ ⟨addr (esp₀ s₀) 4, 16⟩
  rw [addr_eq (by omega), addr_eq (by omega)]
  exact Offset.sub _ hd₁ (by omega)

theorem rin {s : State} (hrd : s.rd = s₀.rd) {d : Nat} (h₁ : 4 ≤ d) (h₂ : d + 4 ≤ 20) :
    InRegions (s.rd ++ s.wr) (addr (esp₀ s₀) d) 4 :=
  ⟨argR s₀, by simp [hrd, hp.rd], hp.arg_in h₁ h₂⟩

/-- The arguments are kept by writes to the state. -/
theorem arg_keep {m : Mem} (hf : Frame [stR s₀ w] s₀.mem m) {d : Nat} (h₁ : 4 ≤ d) (h₂ : d + 4 ≤ 20) :
    m.readW (addr (esp₀ s₀) d) 32 = s₀.mem.readW (addr (esp₀ s₀) d) 32 :=
  hf.readW (r := ⟨addr (esp₀ s₀) d, 4⟩) (Region.contains_self _ _)
    (by simpa using hp.a_st.sub_left (hp.arg_sub h₁ h₂)) (by decide)

theorem st_in {s : State} (hwr : s.wr = s₀.wr) {d n : Nat} (hd : d + n ≤ bufOff w + blockBytes w) (hn : 0 < n) :
    InRegions s.wr (addr (st s₀) d) n :=
  ⟨stR s₀ w, by simp [hwr, hp.wr], contains_addr hd hn hp.st_fit⟩

theorem st_inr {s : State} (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) {d n : Nat}
    (hd : d + n ≤ bufOff w + blockBytes w) (hn : 0 < n) : InRegions (s.rd ++ s.wr) (addr (st s₀) d) n :=
  ⟨stR s₀ w, by simp [hrd, hwr, hp.wr], contains_addr hd hn hp.st_fit⟩

end Pre

/-! ## Bytes -/

theorem writeW_eq (m : Mem) (a : Addr) (v : BitVec 32) : m.writeW a v = writeBytes m a (wordBytes v) := by
  rw [Mem.writeW, write_eq_writeBytes]; rfl

theorem wordBytes_zero : wordBytes (0 : BitVec 32) = List.replicate 4 0 := by decide

theorem writeBytes_at (m : Mem) (q : Addr) (xs : List Byte) {i : Nat} (hi : i < 2 ^ 64) :
    writeBytes m q xs (q + BitVec.ofNat 64 i) = if i < xs.length then xs.getD i 0 else m (q + BitVec.ofNat 64 i) := by
  simp only [writeBytes]
  rw [show q + BitVec.ofNat 64 i - q = BitVec.ofNat 64 i by rw [BitVec.add_comm]; exact BitVec.add_sub_cancel _ _,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi]

/-- The bytes at `q` after writing `xs` there: `xs`, then what was there. -/
theorem bytesAt_writeBytes_prefix (m : Mem) (q : Addr) {xs : List Byte} {n : Nat} (h : xs.length ≤ n)
    (hn : n < 2 ^ 64) :
    bytesAt (writeBytes m q xs) q n = xs ++ bytesAt m (q + BitVec.ofNat 64 xs.length) (n - xs.length) := by
  apply List.ext_getElem (by rw [List.length_append]; simp only [bytesAt, List.length_map, List.length_range]; omega)
  intro i h1 _
  simp only [bytesAt, List.length_map, List.length_range] at h1
  simp only [bytesAt, List.getElem_map, List.getElem_range, writeBytes_at m q xs (by omega : i < 2 ^ 64)]
  by_cases hi : i < xs.length
  · simp [hi, List.getElem_append_left, List.getD_eq_getElem?_getD]
  · rw [List.getElem_append_right (by omega)]
    simp only [hi, ↓reduceIte, List.getElem_map, List.getElem_range, Offset.add_ofNat_add_ofNat,
      show xs.length + (i - xs.length) = i by omega]

/-- The bytes of a run of zeros written at `q`. -/
theorem bytesAt_writeBytes_zeros (m : Mem) (q : Addr) {n a : Nat} (ha : a ≤ n) (hn : n < 2 ^ 64) :
    bytesAt (writeBytes m q (List.replicate n 0)) (q + BitVec.ofNat 64 a) (n - a) = List.replicate (n - a) 0 := by
  apply List.ext_getElem (by simp [bytesAt])
  intro i h1 _
  simp only [bytesAt, List.length_map, List.length_range] at h1
  simp only [bytesAt, List.getElem_map, List.getElem_range, Offset.add_ofNat_add_ofNat,
    writeBytes_at m q _ (by omega : a + i < 2 ^ 64), List.length_replicate, show a + i < n by omega,
    ↓reduceIte, List.getD_eq_getElem?_getD, List.getElem?_replicate, List.getElem_replicate]
  simp

/-! ## The key block -/

/-- During the zero stores. -/
def ZS (s₁ : State) (q : Addr) (j : Nat) (s : State) : Prop :=
  s.gpr = s₁.gpr ∧ s.rd = s₁.rd ∧ s.wr = s₁.wr ∧ s.mem = writeBytes s₁.mem q (List.replicate (4 * j) 0)

theorem zeros_ok {s₀ : State} (hp : Pre P s₀) {s₁ : State} (hax : s₁.gpr .eax = st s₀) (hdx : s₁.gpr .edx = 0)
    (hwr : s₁.wr = s₀.wr) :
    WP isa (.block ((List.range (B w / 4)).flatMap fun j => [.store (at_ .eax (N w + 4 * j)) .edx])) s₁
      (ZS s₁ (stA s₀ + BitVec.ofNat 64 (bufOff w)) (B w / 4)) := by
  have fS := hp.st_fit
  refine wp_range_flatMap (M := isa) (ZS s₁ (stA s₀ + BitVec.ofNat 64 (bufOff w)))
    (fun j s hj ⟨hg, hrd, hwr', hm⟩ => ?_) _ (Nat.le_refl _) s₁
    ⟨rfl, rfl, rfl, by rw [Nat.mul_zero, List.replicate_zero, writeBytes_nil]⟩
  rw [B_eq] at hj
  rw [N_eq]
  have hj4 : bufOff w + 4 * j + 4 ≤ bufOff w + blockBytes w := by omega
  refine wp_stm (B := st s₀) (by rw [hg, hax]) (by rw [hwr', hwr]; exact hp.st_in rfl hj4 (by omega))
    fun s' u' => WP.block_nil ⟨by rw [u'.gpr, hg], by rw [u'.rd, hrd], by rw [u'.wr, hwr'], ?_⟩
  rw [u'.mem, hm, hg, hdx, addr_eq (by omega), writeW_eq, wordBytes_zero, ← Offset.add_add]
  have e := writeBytes_append s₁.mem (stA s₀ + BitVec.ofNat 64 (bufOff w)) (List.replicate (4 * j) 0)
    (List.replicate 4 0) (by simp; omega)
  rw [List.length_replicate] at e
  rw [e, List.replicate_append_replicate, Nat.mul_succ]

/-- After the key block (or none): our caller's `ebx`, `esi`, `edi`, `ebp`
and `esp` are kept, only the state is written, and the buffer holds the key,
padded with zeros, if there is one. -/
structure KB (P : Params w) (s₀ s : State) : Prop where
  gpr : ∀ r ∈ calleeSaved, s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [stR s₀ w] s₀.mem s.mem
  buf : kk s₀ ≠ 0 → bytesAt s.mem (stA s₀ + BitVec.ofNat 64 (bufOff w)) (blockBytes w) =
    K s₀ ++ List.replicate (blockBytes w - kk s₀) 0

theorem keyBlock_ok (hP : Ok P) {s₀ : State} (hp : Pre P s₀) (hk : kk s₀ ≠ 0) {s : State}
    (hax : s.gpr .eax = st s₀) (hcx : s.gpr .ecx = arg s₀ 3)
    (hg : ∀ r ∈ calleeSaved, s.gpr r = s₀.gpr r) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (hm : s.mem = s₀.mem) :
    WP isa (Impl.Blake2.X86.Stream.keyBlock (w := w)) s (KB P s₀) := by
  have hl := hP.len
  have hN := hP.N
  have hmx := hP.max
  have hkk := hp.kk_hi
  have hpos := hP.pos
  have hbb := hP.bb
  have fS := hp.st_fit; have fK := hp.key_fit
  unfold Impl.Blake2.X86.Stream.keyBlock
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine wp_movi fun s₁ u₁ => ?_
  refine WP.mono (zeros_ok hp (by rw [u₁.other _ (by decide), hax]) u₁.gpr (by rw [u₁.wr, hwr]))
    fun s₂ ⟨g₂, rd₂, wr₂, m₂⟩ => ?_
  rw [B_eq, show 4 * (blockBytes w / 4) = blockBytes w by rcases hP.bb with h | h <;> omega] at m₂
  have ax₂ : s₂.gpr .eax = st s₀ := by rw [g₂, u₁.other _ (by decide), hax]
  refine wp_stm (o := 0) ax₂ (by rw [wr₂, u₁.wr, hwr]; exact hp.st_in rfl (by omega) (by omega)) fun s₃ u₃ => ?_
  have sp₃ : s₃.gpr .esp = esp₀ s₀ := by rw [u₃.gpr, g₂, u₁.other _ (by decide), hg _ (by decide)]
  have rd₃ : s₃.rd = s₀.rd := by rw [u₃.rd, rd₂, u₁.rd, hrd]
  have wr₃ : s₃.wr = s₀.wr := by rw [u₃.wr, wr₂, u₁.wr, hwr]
  have m₃ : s₃.mem = (writeBytes s₀.mem (stA s₀ + BitVec.ofNat 64 (bufOff w))
      (List.replicate (blockBytes w) 0)).writeW (addr (st s₀) 0) (s₀.gpr .ebx) := by
    rw [u₃.mem, m₂, u₁.mem, hm, g₂, u₁.other _ (by decide), hg _ (by decide)]
  have F₃ : Frame [stR s₀ w] s₀.mem s₃.mem := by
    rw [m₃]
    exact (writeBytes_frame _ _ _ (contains_offset (by simp only [List.length_replicate]; omega) (by omega))).writeW
      (List.mem_singleton_self _) _ (contains_addr (by omega) (by omega) fS)
  refine wp_ldm sp₃ (hp.rin rd₃ (d := 12) (by omega) (by omega)) fun s₄ u₄ => WP.block_nil ?_
  have dx₄ : s₄.gpr .edx = key s₀ := by rw [u₄.gpr, hp.arg_keep F₃ (by omega) (by omega)]; rfl
  have m₄ : s₄.mem = s₃.mem := u₄.mem
  -- The copy.
  have hk32 : kk s₀ < 2 ^ 32 := (arg s₀ 3).isLt
  refine WP.seq (copyLoop_ok (w := w) (tmp := .bl) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (dA := st s₀) (sA := key s₀) (k := kk s₀) (by omega) hk32 (by omega) (by omega) dx₄
    (by rw [u₄.other _ (by decide), u₃.gpr, ax₂])
    (by rw [u₄.other _ (by decide), u₃.gpr, g₂, u₁.other _ (by decide), hcx]; simp)
    (fun i hi => ⟨keyR s₀, by simp [u₄.rd, rd₃, hp.rd], contains_offset (by omega) (by omega)⟩)
    (fun i hi => by
      rw [u₄.wr, wr₃, addr_eq (by omega)]
      exact ⟨stR s₀ w, by simp [hp.wr], by rw [Offset.add_add]; exact contains_offset (by omega) (by omega)⟩)
    (by rw [addr_eq (by omega)]; exact hp.key_st.sub_right (sub_offset (by omega) (by omega)))
    fun s₅ h₅ => ?_)
  -- The bytes copied are the key's, and the spill is outside them.
  have hK : bytesAt s₄.mem (keyA s₀) (kk s₀) = K s₀ :=
    bytesAt_congr fun i hi => by
      rw [m₄]
      exact F₃.bytes (R := keyR s₀) (by simpa using hp.key_st) (by simp only; omega) hi
  have hm₅ := h₅.mem
  rw [List.take_of_length_le (by simp [bytesAt]), hK, m₄, addr_eq (by omega)] at hm₅
  have rd₅ : s₅.rd = s₀.rd := by rw [h₅.rd, u₄.rd, rd₃]
  have wr₅ : s₅.wr = s₀.wr := by rw [h₅.wr, u₄.wr, wr₃]
  refine wp_ldm (b := .esp) (by rw [h₅.other _ (by decide) (by decide) (by decide) (by decide), u₄.other _ (by decide), sp₃])
    (hp.rin rd₅ (d := 4) (by omega) (by omega)) fun s₆ u₆ => ?_
  have F₅ : Frame [stR s₀ w] s₀.mem s₅.mem := by
    rw [hm₅]
    exact F₃.trans (writeBytes_frame _ _ _ (by
      simp only [bytesAt, List.length_map, List.length_range]; exact contains_offset (by omega) (by omega)))
  have ax₆ : s₆.gpr .eax = st s₀ := by rw [u₆.gpr, hp.arg_keep F₅ (by omega) (by omega)]; rfl
  refine wp_ldm ax₆ (by rw [u₆.rd, u₆.wr, rd₅, wr₅]; exact hp.st_inr rfl rfl (by omega) (by omega))
    fun s₇ u₇ => WP.block_nil ?_
  have m₇ : s₇.mem = s₅.mem := by rw [u₇.mem, u₆.mem]
  -- The spilled `ebx`, outside the buffer.
  have hbx : s₅.mem.readW (addr (st s₀) 0) 32 = s₀.gpr .ebx := by
    rw [hm₅, m₃]
    rw [(writeBytes_frame (R := ⟨stA s₀ + BitVec.ofNat 64 (bufOff w), blockBytes w⟩) _ _ _ (by
      simp only [bytesAt, List.length_map, List.length_range]
      exact Offset.contains _ (Nat.le_refl _) (by omega) (by omega))).readW
      (r := ⟨addr (st s₀) 0, 4⟩) (Region.contains_self _ _) ?_ (by decide), Mem.readW_writeW_self32]
    simp only [List.mem_singleton, forall_eq]
    rw [addr_eq (by omega)]
    exact Offset.disjoint (stA s₀) (by omega) (by omega) (by omega)
  refine ⟨fun r hr => ?_, by rw [u₇.rd, u₆.rd, rd₅], by rw [u₇.wr, u₆.wr, wr₅],
    by rw [m₇]; exact F₅, fun _ => ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [u₇.gpr, u₆.mem, hbx]
    all_goals
      rw [u₇.other _ (by decide), u₆.other _ (by decide), h₅.other _ (by decide) (by decide) (by decide) (by decide),
        u₄.other _ (by decide), u₃.gpr, g₂, u₁.other _ (by decide), hg _ (by decide)]
  · have hKl : (K s₀).length = kk s₀ := by simp [bytesAt]
    rw [m₇, hm₅, m₃, bytesAt_writeBytes_prefix _ _ (by rw [hKl]; omega) (by omega), hKl]
    refine congrArg (K s₀ ++ ·) ?_
    rw [← bytesAt_writeBytes_zeros s₀.mem (stA s₀ + BitVec.ofNat 64 (bufOff w)) (a := kk s₀)
      (n := blockBytes w) (by omega) (by omega)]
    have hf : Frame [⟨addr (st s₀) 0, 4⟩] (writeBytes s₀.mem (stA s₀ + BitVec.ofNat 64 (bufOff w))
        (List.replicate (blockBytes w) 0)) ((writeBytes s₀.mem (stA s₀ + BitVec.ofNat 64 (bufOff w))
        (List.replicate (blockBytes w) 0)).writeW (addr (st s₀) 0) (s₀.gpr .ebx)) :=
      (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
    refine bytesAt_congr fun i hi => ?_
    refine hf.bytes (R := ⟨stA s₀ + BitVec.ofNat 64 (bufOff w) + BitVec.ofNat 64 (kk s₀), blockBytes w - kk s₀⟩)
      ?_ (by simp only; omega) hi
    simp only [List.mem_singleton, forall_eq]
    rw [addr_eq (by omega), Offset.add_add]
    exact Offset.disjoint (stA s₀) (by omega) (by omega) (by omega)

/-! ## The initial hash value -/

theorem wp_xori {is : List Instr} {s : State} {Q : State → Prop} {d : Reg} {v : BitVec 32}
    (k : ∀ s', Upd s s' d (s.gpr d ^^^ v) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .xor d (.imm v) :: is)) s Q :=
  cons rfl (k _ (Upd.flags _ _ _ _ _ _))

/-- During the stores of the IV. -/
def WS (P : Params w) (st : BitVec 32) (s₁ : State) (j : Nat) (s : State) : Prop :=
  (∀ r, r ≠ .ecx → s.gpr r = s₁.gpr r) ∧ s.rd = s₁.rd ∧ s.wr = s₁.wr ∧
    Frame [⟨st.setWidth 64, bufOff w⟩] s₁.mem s.mem ∧ ∀ i < j, s.mem.readW (addr st (4 * i)) 32 = ivWord P i

theorem words_ok (hP : Ok P) {s₀ : State} (hp : Pre P s₀) {s₁ : State} (hax : s₁.gpr .eax = st s₀)
    (hwr : s₁.wr = s₀.wr) :
    WP isa (.block ((List.range (N w / 4)).flatMap fun k =>
      [.mov .ecx (.imm (ivWord P k)), .store (at_ .eax (4 * k)) .ecx])) s₁ (WS P (st s₀) s₁ (N w / 4)) := by
  have fS := hp.st_fit
  have hl := hP.len
  have hbb := hP.bb
  refine wp_range_flatMap (M := isa) (WS P (st s₀) s₁) (fun k s hk ⟨hg, hrd, hwr', hf, hv⟩ => ?_) _
    (Nat.le_refl _) s₁ ⟨fun _ _ => rfl, rfl, rfl, Frame.refl _ _, fun _ h => absurd h (by omega)⟩
  rw [N_eq] at hk
  have hN : bufOff w = blockBytes w / 2 := hP.N
  have hk4 : 4 * k + 4 ≤ bufOff w := by omega
  refine wp_movi fun s₂ u₂ => wp_stm (B := st s₀) (by rw [u₂.other _ (by decide), hg _ (by decide), hax])
    (by rw [u₂.wr, hwr', hwr]; exact hp.st_in rfl (by omega) (by omega)) fun s₃ u₃ => WP.block_nil ?_
  refine ⟨fun r hr => by rw [u₃.gpr, u₂.other r hr, hg r hr], by rw [u₃.rd, u₂.rd, hrd],
    by rw [u₃.wr, u₂.wr, hwr'], ?_, fun i hi => ?_⟩
  · rw [u₃.mem, u₂.mem]
    exact hf.writeW (List.mem_singleton_self _) _ (contains_addr (by omega) (by omega) (by omega))
  · rw [u₃.mem, u₂.gpr, u₂.mem]
    by_cases e : i = k
    · subst e; rw [Mem.readW_writeW_self32]
    · rw [MdStream.X86.readW_writeW_addr _ _ (by omega) (by omega) (by omega)]
      exact hv i (by omega)

theorem rot24 {kk : Nat} (h : kk < 2 ^ 24) :
    (BitVec.ofNat 32 kk).rotateRight 24 = BitVec.ofNat 32 kk <<< 8 := by
  rw [BitVec.rotateRight_def]
  have e : BitVec.ofNat 32 kk >>> (24 % 32) = 0#32 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (by omega)]
    show kk / 2 ^ (24 % 32) = 0
    exact Nat.div_eq_of_lt (by simpa using h)
  rw [e, BitVec.zero_or]

theorem getElem!_IV (P : Params w) {i : Nat} (hi : i < 8) : P.IV[i]! = P.IV[i] := by
  simp [hi]

theorem ivWord32 (P : Params 32) {i : Nat} (hi : i < 8) : ivWord P i = P.IV[i] := by
  simp only [ivWord, Nat.reduceDiv, Nat.div_one, Nat.mod_one, Nat.mul_zero, getElem!_IV P hi,
    BitVec.extractLsb'_eq_self]

theorem ivWord64_lo (P : Params 64) {i : Nat} (hi : i < 8) :
    ivWord P (2 * i) = Proof.Sha512.Word64.lo P.IV[i] := by
  simp only [ivWord, Nat.reduceDiv, Nat.mul_div_cancel_left _ (by decide : 0 < 2), Nat.mul_mod_right,
    Nat.mul_zero, getElem!_IV P hi, Proof.Sha512.Word64.lo]

theorem ivWord64_hi (P : Params 64) {i : Nat} (hi : i < 8) :
    ivWord P (2 * i + 1) = Proof.Sha512.Word64.hi P.IV[i] := by
  have e : (2 * i + 1) / 2 = i := by omega
  have e' : (2 * i + 1) % 2 = 1 := by omega
  simp only [ivWord, Nat.reduceDiv, e, e', Nat.mul_one, getElem!_IV P hi, Proof.Sha512.Word64.hi]

theorem lohi (X : BitVec 64) (x : BitVec 32) (h : X.toNat = x.toNat) :
    Proof.Sha512.Word64.lo X = x ∧ Proof.Sha512.Word64.hi X = 0 := by
  have := x.isLt
  refine ⟨BitVec.eq_of_toNat_eq ?_, BitVec.eq_of_toNat_eq ?_⟩
  · rw [Proof.Sha512.Word64.lo_toNat, h, Nat.mod_eq_of_lt this]
  · rw [Proof.Sha512.Word64.hi_toNat, h, Nat.div_eq_of_lt this]; rfl

/-- The initial hash value, from the words stored. -/
theorem stateAt_init (hP : Ok P) {m : Mem} {st : BitVec 32} (hfit : st.toNat + bufOff w ≤ 2 ^ 32)
    {kk nn : Nat} (hkk : kk < 2 ^ 24) (hnn : nn < 2 ^ 32)
    (h0 : m.readW (addr st 0) 32 =
      ((ivWord P 0 ^^^ 0x01010000) ^^^ (BitVec.ofNat 32 kk).rotateRight 24) ^^^ BitVec.ofNat 32 nn)
    (h : ∀ i, 1 ≤ i → i < bufOff w / 4 → m.readW (addr st (4 * i)) 32 = ivWord P i) :
    stateAt w m (st.setWidth 64) = init P nn kk := by
  apply Vector.ext
  intro j hj
  simp only [stateAt, Vector.getElem_ofFn, Spec.Blake2.init, Vector.getElem_set]
  rcases hP.w with rfl | rfl
  · -- 64-bit words: two 32-bit words each.
    have e₀ : addr st (8 * j) = st.setWidth 64 + BitVec.ofNat 64 (64 / 8 * j) := addr_eq (by simp [bufOff] at hfit; omega)
    have e₁ : addr st (8 * j + 4) = st.setWidth 64 + BitVec.ofNat 64 (64 / 8 * j) + 4 := by
      rw [addr_eq (by simp [bufOff] at hfit; omega), show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl,
        Offset.add_ofNat_add_ofNat]
    rw [Proof.Sha512.Word64.readW64, ← e₁, ← e₀, show 8 * j = 4 * (2 * j) by omega,
      show 4 * (2 * j) + 4 = 4 * (2 * j + 1) by omega]
    have hhi := h (2 * j + 1) (by omega) (by simp [bufOff]; omega)
    rw [hhi, ivWord64_hi P hj]
    by_cases e : j = 0
    · subst e
      simp only [Nat.mul_zero, ↓reduceIte] at h0 ⊢
      have l0 := ivWord64_lo P (i := 0) (by decide)
      rw [Nat.mul_zero] at l0
      rw [h0, l0, rot24 hkk]
      have hC := lohi (((16842752 : Nat) : BitVec 64)) (0x01010000 : BitVec 32) rfl
      have hK := lohi (BitVec.ofNat 64 kk <<< 8) (BitVec.ofNat 32 kk <<< 8) (by
        simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]; omega)
      have hN := lohi (BitVec.ofNat 64 nn) (BitVec.ofNat 32 nn) (by simp only [BitVec.toNat_ofNat]; omega)
      refine Proof.Sha512.Word64.eq_of_lo_hi ?_ ?_
      · rw [Proof.Sha512.Word64.lo_append, Proof.Sha512.Word64.lo_xor, Proof.Sha512.Word64.lo_xor,
          Proof.Sha512.Word64.lo_xor, hC.1, hK.1, hN.1]
      · rw [Proof.Sha512.Word64.hi_append, Proof.Sha512.Word64.hi_xor, Proof.Sha512.Word64.hi_xor,
          Proof.Sha512.Word64.hi_xor, hC.2, hK.2, hN.2]; simp
    · rw [h (2 * j) (by omega) (by simp [bufOff]; omega), ivWord64_lo P hj,
        Proof.Sha512.Word64.hi_append_lo]
      simp [Ne.symm e]
  · have e₀ : addr st (4 * j) = st.setWidth 64 + BitVec.ofNat 64 (32 / 8 * j) := addr_eq (by simp [bufOff] at hfit; omega)
    rw [← e₀]
    by_cases e : j = 0
    · subst e
      simp only [Nat.mul_zero, ↓reduceIte]
      rw [h0, ivWord32 P (by decide), rot24 hkk]; rfl
    · rw [h j (by omega) (by simp [bufOff]; omega), ivWord32 P hj]
      simp [Ne.symm e]

theorem initState_ok (hP : Ok P) {s₀ : State} (hp : Pre P s₀) {s : State} (hrd : s.rd = s₀.rd)
    (hwr : s.wr = s₀.wr) (hsp : s.gpr .esp = esp₀ s₀) (hf : Frame [stR s₀ w] s₀.mem s.mem) :
    WP isa (.block (.mov .eax (.mem (at_ .esp 4)) :: initState P)) s fun s' =>
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [⟨stA s₀, bufOff w⟩] s.mem s'.mem ∧ stateAt w s'.mem (stA s₀) = Spec.Blake2.init P (nn s₀) (kk s₀) := by
  have hl := hP.len
  have hbb := hP.bb
  have hN := hP.N
  have fS := hp.st_fit
  have hkk := hp.kk_hi
  have hmx := hP.max
  refine wp_ldm hsp (hp.rin hrd (d := 4) (by omega) (by omega)) fun s₁ u₁ => ?_
  have ax₁ : s₁.gpr .eax = st s₀ := by rw [u₁.gpr, hp.arg_keep hf (by omega) (by omega)]; rfl
  unfold initState
  rw [WP.block_append_iff]
  refine WP.mono (words_ok hP hp ax₁ (by rw [u₁.wr, hwr])) fun s₂ ⟨g₂, rd₂, wr₂, f₂, v₂⟩ => ?_
  have ax₂ : s₂.gpr .eax = st s₀ := by rw [g₂ _ (by decide), ax₁]
  have hN4 : 0 < N w / 4 := by rw [N_eq]; omega
  have f₂' : Frame [stR s₀ w] s₁.mem s₂.mem := f₂.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨stR s₀ w, by simp, Region.sub_prefix (by omega)⟩
  have F₂ : Frame [stR s₀ w] s₀.mem s₂.mem := hf.trans (u₁.mem ▸ f₂')
  have rd₂' : s₂.rd = s₀.rd := by rw [rd₂, u₁.rd, hrd]
  have wr₂' : s₂.wr = s₀.wr := by rw [wr₂, u₁.wr, hwr]
  have sp₂ : s₂.gpr .esp = esp₀ s₀ := by rw [g₂ _ (by decide), u₁.other _ (by decide), hsp]
  refine wp_ldm ax₂ (hp.st_inr rd₂' wr₂' (by omega) (by omega)) fun s₃ u₃ => ?_
  refine wp_xori fun s₄ u₄ => ?_
  refine wp_ldm (by rw [u₄.other _ (by decide), u₃.other _ (by decide), sp₂])
    (by rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr]; exact hp.rin rd₂' (d := 16) (by omega) (by omega)) fun s₅ u₅ => ?_
  refine wp_ror ⟨by decide, by decide⟩ fun s₆ u₆ => wp_xor fun s₇ u₇ => ?_
  have i8 := hp.rin rd₂' (d := 8) (by omega) (by omega)
  refine wp_xorm (b := .esp) (by rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
    u₄.other _ (by decide), u₃.other _ (by decide), sp₂])
    (by rw [u₇.rd, u₇.wr, u₆.rd, u₆.wr, u₅.rd, u₅.wr, u₄.rd, u₄.wr, u₃.rd, u₃.wr]; exact i8) fun s₈ u₈ => ?_
  refine wp_stm (o := 0) (by rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
    u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), ax₂])
    (by rw [u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr]; exact hp.st_in wr₂' (by omega) (by omega))
    fun s₉ u₉ => WP.block_nil ?_
  have hm₈ : s₈.mem = s₂.mem := by rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem]
  have a16 : s₅.gpr .edx = arg s₀ 3 := by
    rw [u₅.gpr, u₄.mem, u₃.mem, hp.arg_keep F₂ (by omega) (by omega)]; rfl
  have a8 : s₇.mem.readW (addr (esp₀ s₀) 8) 32 = arg s₀ 1 := by
    rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, hp.arg_keep F₂ (by omega) (by omega)]; rfl
  have v₀ : s₂.mem.readW (addr (st s₀) 0) 32 = ivWord P 0 := v₂ 0 hN4
  have hV : s₈.gpr .ecx = ((ivWord P 0 ^^^ 0x01010000) ^^^ (BitVec.ofNat 32 (kk s₀)).rotateRight 24) ^^^
      BitVec.ofNat 32 (nn s₀) := by
    rw [u₈.gpr, a8, u₇.gpr, u₆.gpr, u₆.other _ (by decide), u₅.other _ (by decide), a16, u₄.gpr, u₃.gpr, v₀]
    simp
  have hm₉ : s₉.mem = s₂.mem.writeW (addr (st s₀) 0) (s₈.gpr .ecx) := by rw [u₉.mem, hm₈]
  refine ⟨fun r h1 h2 h3 => ?_, by rw [u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, rd₂, u₁.rd],
    by rw [u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, wr₂, u₁.wr], ?_, ?_⟩
  · rw [u₉.gpr, u₈.other r h2, u₇.other r h2, u₆.other r h3, u₅.other r h3, u₄.other r h2, u₃.other r h2,
      g₂ r h2, u₁.other r h1]
  · rw [hm₉, ← u₁.mem]
    exact f₂.writeW (List.mem_singleton_self _) _ (contains_addr (by omega) (by omega) (by omega))
  · rw [hm₉]
    refine stateAt_init hP (by omega) (by omega) (by have := (arg s₀ 1).isLt; omega)
      (by rw [Mem.readW_writeW_self32, hV]) fun i h1 h2 => ?_
    rw [MdStream.X86.readW_writeW_addr _ _ (by omega) (by omega) (by omega)]
    exact v₂ i (by rw [N_eq]; omega)

/-! ## The whole function -/

theorem correct (hP : Ok P) {s₀ : State} (hp : Pre P s₀) :
    WP isa (Impl.Blake2.X86.Stream.init P) s₀ fun s' => abiPreserved s₀ s' ∧ (initX86 P).post s₀ s' := by
  have hl := hP.len
  have hkk := hp.kk_hi
  have hmx := hP.max
  unfold Impl.Blake2.X86.Stream.init
  refine WP.seq (wp_ldm rfl (hp.rin rfl (d := 4) (by omega) (by omega)) fun s₁ u₁ => ?_)
  refine wp_ldm (by rw [u₁.other _ (by decide)]) (by rw [u₁.rd, u₁.wr]; exact hp.rin rfl (d := 16) (by omega) (by omega))
    fun s₂ u₂ => wp_test fun s₃ f₃ z₃ => WP.block_nil ?_
  have ax₃ : s₃.gpr .eax = st s₀ := by rw [f₃.gpr, u₂.other _ (by decide), u₁.gpr]; rfl
  have cx₃ : s₃.gpr .ecx = arg s₀ 3 := by rw [f₃.gpr, u₂.gpr, u₁.mem]; rfl
  have g₃ : ∀ r ∈ calleeSaved, s₃.gpr r = s₀.gpr r := fun r hr => by
    rw [f₃.gpr, u₂.other r (by simp [calleeSaved] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide),
      u₁.other r (by simp [calleeSaved] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)]
  have rd₃ : s₃.rd = s₀.rd := by rw [f₃.rd, u₂.rd, u₁.rd]
  have wr₃ : s₃.wr = s₀.wr := by rw [f₃.wr, u₂.wr, u₁.wr]
  have m₃ : s₃.mem = s₀.mem := by rw [f₃.mem, u₂.mem, u₁.mem]
  have hz : isa.eval .e s₃ = some (decide (kk s₀ = 0)) := by
    show s₃.zf = _
    rw [z₃, u₂.gpr, u₁.mem, BitVec.and_self]
    show some (arg s₀ 3 == 0) = _
    have := ofNat_beq_zero (arg s₀ 3).isLt
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq] at this
    rw [this]
  refine WP.seq (WP.mono (Q := KB P s₀) ?_ fun s₄ hK => ?_)
  · refine WP.ite _ hz (fun hb => ?_) (fun hb => ?_)
    · simp only [decide_eq_true_eq] at hb
      exact WP.block_nil ⟨g₃, rd₃, wr₃, by rw [m₃]; exact Frame.refl _ _, fun h => absurd hb h⟩
    · simp only [decide_eq_false_iff_not] at hb
      exact keyBlock_ok hP hp hb ax₃ cx₃ g₃ rd₃ wr₃ m₃
  refine WP.mono (initState_ok hP hp hK.rd hK.wr (hK.gpr _ (by decide)) hK.frame)
    fun s₅ ⟨g₅, rd₅, wr₅, f₅, st₅⟩ => ?_
  have F : Frame [stR s₀ w] s₀.mem s₅.mem := hK.frame.trans (f₅.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨stR s₀ w, by simp, Region.sub_prefix (by omega)⟩)
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · rw [g₅ r (by simp [calleeSaved] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)
      (by simp [calleeSaved] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)
      (by simp [calleeSaved] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)]
    exact hK.gpr r hr
  · exact F.readW (Region.contains_self _ _) (by simpa using hp.ret_st) (by decide)
  · show Spec.Blake2.Repr P (Spec.Blake2.init P (nn s₀) (kk s₀)) s₅.mem (stA s₀) (Spec.Blake2.keyBlock w (K s₀))
    have hKl : (K s₀).length = kk s₀ := by simp [bytesAt]
    refine repr_keyBlock P hP.pos (by omega) st₅ fun hk => ?_
    rw [hKl] at hk ⊢
    rw [← hK.buf hk]
    refine bytesAt_congr fun i hi => ?_
    refine f₅.bytes (R := ⟨stA s₀ + BitVec.ofNat 64 (bufOff w), blockBytes w⟩) ?_ (by simp only; omega) hi
    simp only [List.mem_singleton, forall_eq]
    exact Offset.disjoint_base _ (Nat.le_refl _) (by have := hp.st_fit; omega)

end VG.Proof.Blake2.X86.Stream.Init
