import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Spec.MlKem.Poly
import VerifiedGarbage.Proof.MlKem.Arith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.WriteBytes

/-!
# ML-KEM: polynomials and bytes in memory, for every target

How the stored representation of `Spec/MlKem/Poly.lean` (a polynomial as
`[u32; 256]`, `coeffAt`, `polyAt`, `Reduced`, `PolyIs`) and `bytesAt` change
when a program writes a coefficient or a byte, and how to conclude `PolyIs` or
`bytesAt … = L` from what each word or byte holds.
-/

namespace VG.Proof.MlKem

open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-! ## Coefficients -/

/-- The address of coefficient `i` of the polynomial at `p`. -/
abbrev coeffAddr (p : Addr) (i : Nat) : Addr := p + BitVec.ofNat 64 (4 * i)

theorem coeffAt_eq (m : Mem) (p : Addr) (i : Nat) : coeffAt m p i = m.readW (coeffAddr p i) 32 := rfl

/-- The 1024 bytes of a polynomial at `p`. -/
abbrev polyRegion (p : Addr) : Region := ⟨p, 1024⟩

theorem coeff_contains (p : Addr) {i : Nat} (hi : i < n) : (polyRegion p).Contains (coeffAddr p i) 4 := by
  rw [n_eq] at hi; exact Offset.contains_base p (by omega) (by omega)

theorem coeff_sep (p : Addr) {i j : Nat} (hi : i < n) (hj : j < n) (h : i ≠ j) :
    Mem.Sep (coeffAddr p i) 4 (coeffAddr p j) 4 := by
  rw [n_eq] at hi hj; exact Offset.sep p (by omega) (by omega) (by omega)

theorem coeffAt_writeW_self (m : Mem) (p : Addr) (i : Nat) (v : BitVec 32) :
    coeffAt (m.writeW (coeffAddr p i) v) p i = v :=
  Mem.readW_writeW_self32 m _ v

theorem coeffAt_writeW_ne (m : Mem) (p : Addr) {i j : Nat} (hi : i < n) (hj : j < n) (h : i ≠ j)
    (v : BitVec 32) : coeffAt (m.writeW (coeffAddr p j) v) p i = coeffAt m p i :=
  Mem.readW_writeW_sep (coeff_sep p hi hj h) (by decide)

/-- Writing coefficient `j` of the polynomial at `p`. -/
theorem coeffAt_writeW (m : Mem) (p : Addr) {i j : Nat} (hi : i < n) (hj : j < n) (v : BitVec 32) :
    coeffAt (m.writeW (coeffAddr p j) v) p i = if j = i then v else coeffAt m p i := by
  split
  · subst j; exact coeffAt_writeW_self m p i v
  · exact coeffAt_writeW_ne m p hi hj (Ne.symm ‹_›) v

/-- Writing `w` bits at `a`, apart from coefficient `i`. -/
theorem coeffAt_writeW_sep (m : Mem) (p : Addr) {i : Nat} {a : Addr} {w : Nat} (v : BitVec w)
    (h : Mem.Sep (coeffAddr p i) 4 a (w / 8)) : coeffAt (m.writeW a v) p i = coeffAt m p i :=
  Mem.readW_writeW_sep h (by decide)

/-- Coefficient `i` of `polyAt`: the stored word modulo `q`. -/
theorem polyAt_get (m : Mem) (p : Addr) {i : Nat} (hi : i < n) :
    (polyAt m p)[i]! = ofNat (coeffAt m p i).toNat := by
  rw [getElem!_eq _ hi]
  simp only [polyAt, Vector.getElem_ofFn]

/-- Coefficient `i` of a reduced polynomial is the stored word. -/
theorem polyAt_val {m : Mem} {p : Addr} (hr : Reduced m p) {i : Nat} (hi : i < n) :
    ((polyAt m p)[i]!).val = (coeffAt m p i).toNat := by
  rw [polyAt_get m p hi, ofNat_of_lt (hr i hi)]

/-- The polynomial after writing coefficient `j`. -/
theorem polyAt_writeW (m : Mem) (p : Addr) {j : Nat} (hj : j < n) (v : BitVec 32) :
    polyAt (m.writeW (coeffAddr p j) v) p = (polyAt m p).set! j (ofNat v.toNat) := by
  refine ext_getElem! fun i hi => ?_
  rw [polyAt_get _ _ hi, coeffAt_writeW m p hi hj]
  split
  · subst j; rw [getElem!_set!_self _ hi]
  · rw [getElem!_set!_ne _ hi ‹_›, polyAt_get _ _ hi]

theorem reduced_writeW {m : Mem} {p : Addr} (hr : Reduced m p) {j : Nat} (hj : j < n) {v : BitVec 32}
    (hv : v.toNat < q) : Reduced (m.writeW (coeffAddr p j) v) p := fun i hi => by
  rw [coeffAt_writeW m p hi hj]
  split
  · exact hv
  · exact hr i hi

/-- The word stored for coefficient `i` of `f`. -/
theorem polyIs_toNat {m : Mem} {p : Addr} {f : Poly} (h : PolyIs m p f) {i : Nat} (hi : i < n) :
    (coeffAt m p i).toNat = (f[i]!).val := by
  rw [← h.2, polyAt_val h.1 hi]

theorem polyIs_coeffAt {m : Mem} {p : Addr} {f : Poly} (h : PolyIs m p f) {i : Nat} (hi : i < n) :
    coeffAt m p i = BitVec.ofNat 32 (f[i]!).val := by
  apply BitVec.eq_of_toNat_eq
  rw [polyIs_toNat h hi, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := val_lt f[i]!; omega)]

/-- `f` is stored at `p` if each of its coefficients is. -/
theorem polyIs_of_toNat {m : Mem} {p : Addr} {f : Poly}
    (h : ∀ i < n, (coeffAt m p i).toNat = (f[i]!).val) : PolyIs m p f := by
  refine ⟨fun i hi => by rw [h i hi]; exact (f[i]!).isLt, ext_getElem! fun i hi => ?_⟩
  rw [polyAt_get _ _ hi, h i hi, ofNat_val]

/-- `f` is stored at `p` if each of its coefficients is. -/
theorem polyIs_of_coeffAt {m : Mem} {p : Addr} {f : Poly}
    (h : ∀ i < n, coeffAt m p i = BitVec.ofNat 32 (f[i]!).val) : PolyIs m p f :=
  polyIs_of_toNat fun i hi => by
    rw [h i hi, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := val_lt f[i]!; omega)]

/-- Writing a coefficient of a stored polynomial. -/
theorem polyIs_writeW {m : Mem} {p : Addr} {f : Poly} (h : PolyIs m p f) {j : Nat} (hj : j < n)
    (x : Zq) : PolyIs (m.writeW (coeffAddr p j) (BitVec.ofNat 32 x.val)) p (f.set! j x) := by
  have hx : (BitVec.ofNat 32 x.val).toNat = x.val := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := val_lt x; omega)]
  refine ⟨reduced_writeW h.1 hj (by rw [hx]; exact x.isLt), ?_⟩
  rw [polyAt_writeW m p hj, hx, ofNat_val, h.2]

/-! ## Frames: the polynomial is unchanged by writes elsewhere -/

theorem coeffAt_congr {m m' : Mem} {p : Addr}
    (h : ∀ k < 1024, m' (p + BitVec.ofNat 64 k) = m (p + BitVec.ofNat 64 k)) {i : Nat} (hi : i < n) :
    coeffAt m' p i = coeffAt m p i := by
  rw [n_eq] at hi
  refine Mem.readW_congr fun k hk => ?_
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  exact h _ (by omega)

theorem polyAt_congr {m m' : Mem} {p : Addr}
    (h : ∀ k < 1024, m' (p + BitVec.ofNat 64 k) = m (p + BitVec.ofNat 64 k)) :
    polyAt m' p = polyAt m p :=
  ext_getElem! fun i hi => by rw [polyAt_get _ _ hi, polyAt_get _ _ hi, coeffAt_congr h hi]

theorem reduced_congr {m m' : Mem} {p : Addr}
    (h : ∀ k < 1024, m' (p + BitVec.ofNat 64 k) = m (p + BitVec.ofNat 64 k)) (hr : Reduced m p) :
    Reduced m' p := fun i hi => by rw [coeffAt_congr h hi]; exact hr i hi

theorem polyIs_congr {m m' : Mem} {p : Addr} {f : Poly}
    (h : ∀ k < 1024, m' (p + BitVec.ofNat 64 k) = m (p + BitVec.ofNat 64 k)) (hf : PolyIs m p f) :
    PolyIs m' p f := ⟨reduced_congr h hf.1, (polyAt_congr h).trans hf.2⟩

theorem bytes_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {len : Nat}
    (hd : ∀ r ∈ rs, (⟨p, len⟩ : Region).Disjoint r) (hlen : len ≤ 2 ^ 64) :
    ∀ k < len, m' (p + BitVec.ofNat 64 k) = m (p + BitVec.ofNat 64 k) :=
  fun _ hk => hf.bytes (R := ⟨p, len⟩) hd hlen hk

theorem polyAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, (polyRegion p).Disjoint r) : polyAt m' p = polyAt m p :=
  polyAt_congr (bytes_frame hf hd (by decide))

theorem reduced_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, (polyRegion p).Disjoint r) (hr : Reduced m p) : Reduced m' p :=
  reduced_congr (bytes_frame hf hd (by decide)) hr

theorem polyIs_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {f : Poly}
    (hd : ∀ r ∈ rs, (polyRegion p).Disjoint r) (h : PolyIs m p f) : PolyIs m' p f :=
  polyIs_congr (bytes_frame hf hd (by decide)) h

/-! ## Bytes -/

theorem bytesAt_length (m : Mem) (p : Addr) (len : Nat) : (bytesAt m p len).length = len := by
  simp [bytesAt]

theorem bytesAt_getElem (m : Mem) (p : Addr) {len i : Nat} (hi : i < (bytesAt m p len).length) :
    (bytesAt m p len)[i] = m (p + BitVec.ofNat 64 i) := by
  simp [bytesAt]

theorem bytesAt_getD (m : Mem) (p : Addr) {len i : Nat} (hi : i < len) :
    (bytesAt m p len).getD i 0 = m (p + BitVec.ofNat 64 i) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [bytesAt_length]; exact hi),
    Option.getD_some, bytesAt_getElem]

theorem bytesAt_getElem! (m : Mem) (p : Addr) {len i : Nat} (hi : i < len) :
    (bytesAt m p len)[i]! = m (p + BitVec.ofNat 64 i) := by
  rw [getElem!_pos _ _ (by rw [bytesAt_length]; exact hi), bytesAt_getElem]

theorem bytesAt_add (m : Mem) (p : Addr) (a b : Nat) :
    bytesAt m p (a + b) = bytesAt m p a ++ bytesAt m (p + BitVec.ofNat 64 a) b := by
  simp only [bytesAt, List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  show m _ = m _
  rw [BitVec.add_assoc, BitVec.ofNat_add]

theorem bytesAt_take (m : Mem) (p : Addr) {k len : Nat} (h : k ≤ len) :
    (bytesAt m p len).take k = bytesAt m p k := by
  rw [show len = k + (len - k) by omega, bytesAt_add, List.take_left' (bytesAt_length _ _ _)]

theorem bytesAt_drop (m : Mem) (p : Addr) {k len : Nat} (h : k ≤ len) :
    (bytesAt m p len).drop k = bytesAt m (p + BitVec.ofNat 64 k) (len - k) := by
  rw [show len = k + (len - k) by omega, bytesAt_add, List.drop_left' (bytesAt_length _ _ _),
    Nat.add_sub_cancel_left]

/-- `(B.drop k).take c` of the bytes at `p`: the `c` bytes at `p + k`. -/
theorem bytesAt_slice (m : Mem) (p : Addr) {k c len : Nat} (h : k + c ≤ len) :
    ((bytesAt m p len).drop k).take c = bytesAt m (p + BitVec.ofNat 64 k) c := by
  rw [bytesAt_drop m p (by omega), bytesAt_take _ _ (by omega)]

theorem bytesAt_congr {m m' : Mem} {p : Addr} {len : Nat}
    (h : ∀ i < len, m' (p + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i)) :
    bytesAt m' p len = bytesAt m p len :=
  List.map_congr_left fun i hi => h i (List.mem_range.mp hi)

/-- The bytes at `p` are `L` if each is. -/
theorem bytesAt_eq {m : Mem} {p : Addr} {L : List Byte} {len : Nat} (hl : L.length = len)
    (h : ∀ i (hi : i < len), m (p + BitVec.ofNat 64 i) = L[i]'(by omega)) : bytesAt m p len = L :=
  List.ext_getElem (by rw [bytesAt_length, hl]) fun i h₁ _ => by
    rw [bytesAt_getElem]; exact h i (by rw [bytesAt_length] at h₁; exact h₁)

/-- The bytes at `p` are `L` if each is (with `L[i]!`, as the lemmas of
`Encode.lean` state bytes). -/
theorem bytesAt_eq! {m : Mem} {p : Addr} {L : List Byte} {len : Nat} (hl : L.length = len)
    (h : ∀ i < len, m (p + BitVec.ofNat 64 i) = L[i]!) : bytesAt m p len = L :=
  bytesAt_eq hl fun i hi => by rw [h i hi, getElem!_pos L i (by omega)]

theorem bytesAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {len : Nat}
    (hd : ∀ r ∈ rs, (⟨p, len⟩ : Region).Disjoint r) (hlen : len ≤ 2 ^ 64) :
    bytesAt m' p len = bytesAt m p len :=
  bytesAt_congr (bytes_frame hf hd hlen)

export VG.WriteBytes (writeW8_apply)

/-- Writing byte `i` of the bytes at `p`. -/
theorem bytesAt_writeW8 (m : Mem) (p : Addr) {i len : Nat} (hi : i < len) (hlen : len ≤ 2 ^ 64)
    (b : Byte) : bytesAt (m.writeW (p + BitVec.ofNat 64 i) b) p len = (bytesAt m p len).set i b := by
  refine List.ext_getElem (by simp [bytesAt_length]) fun k h₁ h₂ => ?_
  rw [bytesAt_getElem, List.getElem_set, bytesAt_getElem, writeW8_apply]
  rw [bytesAt_length] at h₁
  by_cases hk : i = k
  · subst hk; simp
  · have : p + BitVec.ofNat 64 k ≠ p + BitVec.ofNat 64 i := by
      intro e
      apply hk
      bv_omega
    simp [this, hk]

/-- Writing a byte apart from the bytes at `p`. -/
theorem bytesAt_writeW_sep (m : Mem) (p : Addr) {len : Nat} {a : Addr} {w : Nat} (v : BitVec w)
    (h : Mem.Sep p len a (w / 8)) (hlen : len < 2 ^ 64) :
    bytesAt (m.writeW a v) p len = bytesAt m p len :=
  bytesAt_congr fun i hi => Mem.write_apply (h _ (by rw [Mem.sub_ofNat_toNat p (by omega)]; exact hi))

end VG.Proof.MlKem
