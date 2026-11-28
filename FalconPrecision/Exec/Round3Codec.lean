/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import FalconPrecision.Exec.KeyCheck

/-! # Round-3 key decoding

Executable decoders of the round-3 encodings (Falcon specification v1.2, §3.11) at degree
`n = 2^logn` (default Falcon-512, `logn = 9`):

* `decodeSk`: a private key (§3.11.5, p. 49) is the header byte `0101nnnn` (`nnnn = logn`; `0x59`
  at `n = 512`), then `f`, `g` over `fgBits` bits per coefficient (default `fgBitsOf logn`: 6 at
  `n = 512`, 5 at `n = 1024`) and `F` over 8 bits, two's complement, most significant bit first
  (§3.11.1, p. 46); the minimal value `-2^(w-1)` is rejected; exactly `1 + (2·fgBits + 8)·n/8`
  bytes (1281 at `n = 512`, 2305 at `n = 1024`; the bit length is a multiple of 8: no padding bits).
* `decodePk`: a public key (§3.11.4, p. 49) is the header byte `0000nnnn` (`0x09` at `n = 512`),
  then `h` over 14 bits per coefficient, every value `< q`; exactly `1 + ⌈14n/8⌉` bytes (897 at
  `n = 512`, 1793 at `n = 1024`).
* Both decoders return `none` unless `1 ≤ logn ≤ 10` (§3.11.4-5: "ℓ must be in the allowed range (1
  to 10)"), so the header byte is `0x50 + logn` (resp. `logn`) without overflow.
* `solveG`: `G = (q + gF)/f mod φ` (eq. (3.35), p. 50) computed modulo `q` at the points
  `ω^(2i+1)` (`ω = 7^(2^(10 - logn))`, of order `2n` for `logn ≤ 10`; `7²` at `n = 512`),
  `G ≡ g·F·f⁻¹`, lifted to `(-q/2, q/2]`; `none` for `logn > 10` (outside the spec's range 1 to
  10). It is not proved that the result satisfies `fG - gF = q`: `ntruB` decides it on the
  `RawKey`, exactly in `ℤ[x]/(xⁿ + 1)`.
* `pkMatchB`: `h·f ≡ g (mod q)` in `ℤ[x]/(xⁿ + 1)` (`ncoef`), decided. -/

@[expose] public section

namespace FalconPrecision.Exec.Round3

/-- Falcon's modulus `q = 12289`. -/
def qN : ℕ := 12289

/-! ## Bytes and bits -/

/-- The value of a hexadecimal digit. -/
def hexVal (c : Char) : Option ℕ :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

/-- The bytes of a hexadecimal string of even length. -/
def ofHex (s : String) : Option ByteArray := do
  let cs := s.toList.toArray
  guard (cs.size % 2 = 0)
  (Array.range (cs.size / 2)).foldlM (init := ByteArray.empty) fun out i => do
    let hi ← hexVal cs[2 * i]!
    let lo ← hexVal cs[2 * i + 1]!
    pure (out.push (16 * hi + lo).toUInt8)

/-- Bit `k` of a byte string; within a byte the most significant bit comes first (§3.11.1). -/
def bit (b : ByteArray) (k : ℕ) : ℕ := (b[k / 8]!.toNat >>> (7 - k % 8)) % 2

/-- The `w`-bit value at bit offset `p`, most significant bit first. -/
def bitsAt (b : ByteArray) (p w : ℕ) : ℕ :=
  (List.range w).foldl (fun a j => 2 * a + bit b (p + j)) 0

/-- A `w`-bit two's-complement value; the minimal value `-2^(w-1)` is rejected (§3.11.5). -/
def signedOf (w v : ℕ) : Option ℤ :=
  if v < 2 ^ (w - 1) then some v
  else if v = 2 ^ (w - 1) then none
  else some ((v : ℤ) - 2 ^ w)

/-- `cnt` signed `w`-bit coefficients from bit offset `p`. -/
def signedPoly (b : ByteArray) (p w cnt : ℕ) : Option (Array ℤ) :=
  (Array.range cnt).mapM fun i => signedOf w (bitsAt b (p + w * i) w)

/-! ## Decoders -/

/-- The width of the coefficients of `f` and `g` in a private key of degree `2^logn` (§3.11.5):
"8 bits each for degrees 2 to 32; 7 bits each for degrees 64 and 128; 6 bits each for degrees 256
and 512; 5 bits each for degree 1024". Meaningful for `1 ≤ logn ≤ 10`. -/
def fgBitsOf (logn : ℕ) : ℕ :=
  if logn ≤ 5 then 8 else if logn ≤ 7 then 7 else if logn ≤ 9 then 6 else 5

/-- A private key `(f, g, F)` of degree `2^logn`, `f`, `g` over `fgBits` bits (default
`fgBitsOf logn`) (§3.11.5); `none` unless `1 ≤ logn ≤ 10` (the spec's range). -/
def decodeSk (b : ByteArray) (logn : ℕ := 9) (fgBits : ℕ := fgBitsOf logn) :
    Option (Array ℤ × Array ℤ × Array ℤ) := do
  guard (1 ≤ logn ∧ logn ≤ 10)
  guard (b.size = 1 + (2 * fgBits + 8) * 2 ^ logn / 8 ∧ b[0]! = Nat.toUInt8 (0x50 + logn))
  let f ← signedPoly b 8 fgBits (2 ^ logn)
  let g ← signedPoly b (8 + fgBits * 2 ^ logn) fgBits (2 ^ logn)
  let F ← signedPoly b (8 + 2 * fgBits * 2 ^ logn) 8 (2 ^ logn)
  pure (f, g, F)

/-- A public key `h` of degree `2^logn`, coefficients in `[0, q)`, `1 + ⌈14n/8⌉` bytes (§3.11.4);
`none` unless `1 ≤ logn ≤ 10` (the spec's range). -/
def decodePk (b : ByteArray) (logn : ℕ := 9) : Option (Array ℕ) := do
  guard (1 ≤ logn ∧ logn ≤ 10)
  guard (b.size = 1 + (14 * 2 ^ logn + 7) / 8 ∧ b[0]! = Nat.toUInt8 logn)
  (Array.range (2 ^ logn)).mapM fun i =>
    let v := bitsAt b (8 + 14 * i) 14
    if v < qN then some v else none

/-! ## `G` modulo `q` -/

/-- `a^e mod q` for `e < 2¹⁴`. -/
def powq (a e : ℕ) : ℕ := Id.run do
  let mut r := 1
  let mut x := a % qN
  let mut k := e
  for _ in [0:14] do
    if k % 2 = 1 then r := r * x % qN
    x := x * x % qN
    k := k / 2
  return r

/-- `ω = 7^(2^(10 - logn)) mod q`, of order `2^(logn + 1)` for `logn ≤ 10` (`7` has order
`2048`); `7²` at `logn = 9`. Only meaningful for `logn ≤ 10` (`10 - logn` truncates above):
`pts`, `nttq`, `inttq` assume that range, and `solveG` returns `none` outside it. -/
def ωOf (logn : ℕ) : ℕ := powq 7 (2 ^ (10 - logn))

/-- `ω` at Falcon-512: `7² mod q`, of order `1024`. -/
def ω : ℕ := ωOf 9

/-- The points `ω^(2i+1)`, `i < 2^logn`: the roots of `x^(2^logn) + 1` modulo `q`. -/
def pts (logn : ℕ := 9) : Array ℕ :=
  (Array.range (2 ^ logn)).map fun i => powq (ωOf logn) (2 * i + 1)

/-- `c mod q` in `[0, q)`. -/
def modq (c : ℤ) : ℕ := (c % (qN : ℤ)).toNat

/-- The value of a polynomial at `x` modulo `q`. -/
def evalq (a : Array ℕ) (x : ℕ) : ℕ := a.foldr (fun c s => (s * x + c) % qN) 0

/-- Values at `pts logn`. -/
def nttq (a : Array ℤ) (logn : ℕ := 9) : Array ℕ := (pts logn).map (evalq (a.map modq))

/-- Coefficients from values at `pts logn`: `aⱼ = n⁻¹ Σᵢ Aᵢ·ptsᵢ⁻ʲ` (`n = 2^logn`). -/
def inttq (A : Array ℕ) (logn : ℕ := 9) : Array ℕ := Id.run do
  let n := 2 ^ logn
  let ninv := powq n (qN - 2)
  let ys := (pts logn).map fun x => powq x (qN - 2)
  let mut p := Array.replicate n 1
  let mut out := Array.mkEmpty n
  for _ in [0:n] do
    let s := (List.range n).foldl (fun s i => (s + A[i]! * p[i]!) % qN) 0
    out := out.push (s * ninv % qN)
    p := (Array.range n).map fun i => p[i]! * ys[i]! % qN
  return out

/-- The lift of a residue to `(-q/2, q/2]`. -/
def centre (v : ℕ) : ℤ := if v ≤ qN / 2 then v else (v : ℤ) - qN

/-- `G ≡ g·F·f⁻¹ (mod q)`, centred; `none` if `logn > 10` (no `ωOf logn`) or `f` is not
invertible modulo `q` at `pts`. -/
def solveG (f g F : Array ℤ) (logn : ℕ := 9) : Option (Array ℤ) := do
  guard (logn ≤ 10)
  let fh := nttq f logn
  let gh := nttq g logn
  let Fh := nttq F logn
  guard (fh.all (· ≠ 0))
  let Gh := (Array.range (2 ^ logn)).map fun i => gh[i]! * Fh[i]! % qN * powq fh[i]! (qN - 2) % qN
  pure ((inttq Gh logn).map centre)

/-! ## Raw keys -/

/-- A coefficient array as a polynomial of size `2^logn` (missing entries `0`). -/
def polyOf (a : Array ℤ) (logn : ℕ := 9) : Fin (2 ^ logn) → ℤ := fun i => a.getD i.1 0

/-- The raw key of a decoded private key, `G` from `solveG`. -/
def decodeKey (sk : ByteArray) (logn : ℕ := 9) (fgBits : ℕ := fgBitsOf logn) :
    Option (RawKey logn) := do
  let (f, g, F) ← decodeSk sk logn fgBits
  let G ← solveG f g F logn
  pure ⟨polyOf f logn, polyOf g logn, polyOf F logn, polyOf G logn⟩

/-- `h·f ≡ g (mod q)` in `ℤ[x]/(x^(2^logn) + 1)`, decided. -/
def pkMatchB {logn : ℕ} (h : Array ℕ) (k : RawKey logn) : Bool :=
  decide (∀ i : Fin (2 ^ logn),
    (ncoef (polyOf (h.map (Int.ofNat ·)) logn) k.f i - k.g i) % (qN : ℤ) = 0)

end FalconPrecision.Exec.Round3
