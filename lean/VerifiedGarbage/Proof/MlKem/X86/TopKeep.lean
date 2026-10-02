import VerifiedGarbage.Proof.MlKem.X86.TopLocal

/-!
# ML-KEM on x86 (32-bit): what a call leaves unchanged

A buffer apart from the regions a call or a block changes (`Frame`) keeps its
bytes (`keep`), and so the polynomial, bytes or word it holds (`keepPoly`,
`keepBytes`, `keepW`, `keepRed`), when its separation from them is computed
(`decide`). The bytes of a buffer are those of its two parts (`bytes_split`).
The body of a top-level function, which ends in `Ctx`, makes a leaf
(`topLeaf`).
-/

namespace VG.Proof.MlKem.X86.Top

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem
open VG.Proof.MlKem.X86
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

variable {Y : Lay} {s₀ : State}

/-- The frame of a block or call: buffers, and the stack below the leaf's frame. -/
abbrev FR (s₀ : State) (bs : List Buf) (N : Nat) : List Region :=
  bs.map (Buf.rgn s₀) ++ [below (E1 s₀) N]

/-- Whether `b` is a buffer apart from each of `bs`. -/
def Lay.apart (Y : Lay) (b : Buf) (bs : List Buf) : Bool := Y.ok b && bs.all fun c => Y.ok c && Y.sep b c

theorem keep (hp : TPre Y s₀) {bs : List Buf} {N : Nat} (hN : N + 16 ≤ Y.stk) {b : Buf} (hs : Y.apart b bs = true)
    {m m' : Mem} (fr : Frame (FR s₀ bs N) m m') :
    ∀ i < b.len, m' (b.addr s₀ + BitVec.ofNat 64 i) = m (b.addr s₀ + BitVec.ofNat 64 i) := by
  simp only [Lay.apart, Bool.and_eq_true] at hs
  exact bytes_frame fr (Buf.frD hp hs.1 hs.2 hN) (by have := Buf.fit hp hs.1; omega)

theorem keepPoly (hp : TPre Y s₀) {bs : List Buf} {N : Nat} (hN : N + 16 ≤ Y.stk) {a o : Nat}
    (hs : Y.apart ⟨a, o, 1024⟩ bs = true) {m m' : Mem} (fr : Frame (FR s₀ bs N) m m') {f : Poly}
    (h : PolyIs m (Buf.addr s₀ ⟨a, o, 1024⟩) f) : PolyIs m' (Buf.addr s₀ ⟨a, o, 1024⟩) f :=
  polyIs_congr (keep hp hN hs fr) h

theorem keepRed (hp : TPre Y s₀) {bs : List Buf} {N : Nat} (hN : N + 16 ≤ Y.stk) {a o : Nat}
    (hs : Y.apart ⟨a, o, 1024⟩ bs = true) {m m' : Mem} (fr : Frame (FR s₀ bs N) m m')
    (h : Reduced m (Buf.addr s₀ ⟨a, o, 1024⟩)) : Reduced m' (Buf.addr s₀ ⟨a, o, 1024⟩) :=
  reduced_congr (keep hp hN hs fr) h

theorem keepBytes (hp : TPre Y s₀) {bs : List Buf} {N : Nat} (hN : N + 16 ≤ Y.stk) {b : Buf}
    (hs : Y.apart b bs = true) {m m' : Mem} (fr : Frame (FR s₀ bs N) m m') :
    bytesAt m' (b.addr s₀) b.len = bytesAt m (b.addr s₀) b.len :=
  bytesAt_congr (keep hp hN hs fr)

theorem keepW (hp : TPre Y s₀) {bs : List Buf} {N : Nat} (hN : N + 16 ≤ Y.stk) {a o : Nat}
    (hs : Y.apart ⟨a, o, 4⟩ bs = true) {m m' : Mem} (fr : Frame (FR s₀ bs N) m m') :
    m'.readW (Buf.addr s₀ ⟨a, o, 4⟩) 32 = m.readW (Buf.addr s₀ ⟨a, o, 4⟩) 32 :=
  Mem.readW_congr fun i hi => keep hp hN hs fr i hi

/-- A single region, as a frame. -/
theorem fr1 {b : Buf} {m m' : Mem} (fr : Frame [b.rgn s₀] m m') : Frame (FR s₀ [b] 0) m m' :=
  fr.mono (by simp)

/-- Two regions, as a frame. -/
theorem fr2 {b c : Buf} {m m' : Mem} (fr : Frame [b.rgn s₀, c.rgn s₀] m m') : Frame (FR s₀ [b, c] 0) m m' :=
  fr.mono (by simp)

/-- A byte written. -/
theorem frW8 {o : Nat} {m : Mem} {v : Byte} :
    Frame (FR s₀ [⟨Y.sc, o, 1⟩] 0) m (m.writeW (Buf.addr s₀ ⟨Y.sc, o, 1⟩) v) :=
  fr1 ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (by
    show (⟨Buf.addr s₀ ⟨Y.sc, o, 1⟩, 1⟩ : Region).Contains _ (8 / 8); exact Region.contains_self _ _))

/-- A word written. -/
theorem frW32 {o : Nat} {m : Mem} {v : BitVec 32} :
    Frame (FR s₀ [⟨Y.sc, o, 4⟩] 0) m (m.writeW (Buf.addr s₀ ⟨Y.sc, o, 4⟩) v) :=
  fr1 ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (by
    show (⟨Buf.addr s₀ ⟨Y.sc, o, 4⟩, 4⟩ : Region).Contains _ (32 / 8); exact Region.contains_self _ _))

/-- The bytes of a buffer, as those of its two parts. -/
theorem bytes_split (hp : TPre Y s₀) (m : Mem) {a o o' l₁ l₂ L : Nat} (ho : o + l₁ = o') (hL : l₁ + l₂ = L)
    (h₁ : Y.ok ⟨a, o, l₁⟩ = true) (h₂ : Y.ok ⟨a, o', l₂⟩ = true) :
    bytesAt m (Buf.addr s₀ ⟨a, o, L⟩) L =
      bytesAt m (Buf.addr s₀ ⟨a, o, l₁⟩) l₁ ++ bytesAt m (Buf.addr s₀ ⟨a, o', l₂⟩) l₂ := by
  have e : Buf.addr s₀ ⟨a, o', l₂⟩ = Buf.addr s₀ ⟨a, o, l₁⟩ + BitVec.ofNat 64 l₁ := by
    rw [Buf.addr_eq hp h₂, Buf.addr_eq hp h₁, BitVec.add_assoc, ← BitVec.ofNat_add, ho]
  rw [e, ← hL]
  exact bytesAt_add m _ l₁ l₂

/-- A top-level function, from its body. -/
theorem topLeaf {lk : State → List Byte} {body : Prog isa} {B : State → State → Prop} (hsp : NoSp body)
    (hb : Piece (TPre Y) (TPub Y lk) (fun s₀ s => s = P0 s₀) (fun s₀ s => Ctx Y s₀ s ∧ B s₀ s) body) :
    Piece (TPre Y) (TPub Y lk) (fun s₀ s => s = s₀) (fun s₀ s' => LeafPost (B s₀) s₀ s') (leaf body) :=
  Piece.leaf (W Y) hsp (fun _ hp => ⟨hp.E0_big, by have := hp.sp'; omega⟩) (fun _ hp => hp.hW)
    (fun _ _ _ _ hq => hq.1) (hb.mono (fun _ _ _ h => h) fun _ _ _ h => ⟨⟨h.1.frame, h.1.esp, h.1.rd, h.1.wr⟩, h.2⟩)

end VG.Proof.MlKem.X86.Top
